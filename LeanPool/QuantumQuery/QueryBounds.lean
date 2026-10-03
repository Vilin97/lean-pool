/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import LeanPool.QuantumQuery.StateConversion

/-!
# Operational adversary lower bounds and query characterizations

Ported from the corresponding upstream modules listed by the source sections below.
References beginning with `Source` name these retained sections.
-/

public section

section SourceQuantumLowerBoundBridge

/-!
# The real-matrix / complex-vector bridge

The adversary side of this project is real: `advPMOn` is a supremum of L2
operator norms of **real** matrices, and `SourceSpectral` supplies the bilinear
bound `|x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ √(x⬝ᵥx) √(y⬝ᵥy)`.  The quantum side is complex.  The
progress measure of the lower bound lives in between: it is a real matrix `Γ`
contracted against a family of **complex** vectors,

  `∑ x, ∑ y, Γ x y * Re ⟪u x, v y⟫`.

This section proves the one inequality that connects them,

  `|∑ x, ∑ y, Γ x y * Re ⟪u x, v y⟫| ≤ ‖Γ‖ · √(∑ x, ‖u x‖²) · √(∑ y, ‖v y‖²)`,

which is Risk 2 of the plan discharged: no complex operator-norm theory is
needed, and the existing real API is used unchanged.

The proof is the obvious one once the real part is expanded coordinatewise:
`Re ⟪u, v⟫ = ∑ h, (Re uₕ Re vₕ + Im uₕ Im vₕ)`, so the double sum is
`∑ h, (aᵣ(h) ⬝ᵥ Γ *ᵥ bᵣ(h) + aᵢ(h) ⬝ᵥ Γ *ᵥ bᵢ(h))`, a sum over the basis of
**real** bilinear forms.  Bounding each by `SourceSpectral` and applying
Cauchy–Schwarz twice — once to combine the real and imaginary parts at a fixed
basis vector, once to sum over the basis — gives the claim.  Working with the
real part throughout (rather than the complex Gram value and its modulus) is
what keeps this elementary; the progress measure is defined with `Re` for the
same reason.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- The real part of the inner product, expanded over the basis. -/
lemma qInner_re (ψ φ : H → ℂ) :
    (qInner ψ φ).re = ∑ h, ((ψ h).re * (φ h).re + (ψ h).im * (φ h).im) := by
  classical
  rw [qInner_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [Complex.mul_re]

omit [DecidableEq H] in
/-- The squared norm, expanded over the basis. -/
lemma qNormSq_eq_sum_re_im (ψ : H → ℂ) :
    qNormSq ψ = ∑ h, ((ψ h).re * (ψ h).re + (ψ h).im * (ψ h).im) := by
  classical
  rw [qNormSq_def]
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_apply (ψ h)

omit [DecidableEq H] in
/-- Scaling a state by a real number. -/
lemma qNormSq_real_smul (c : ℝ) (ψ : H → ℂ) :
    qNormSq ((c : ℂ) • ψ) = c ^ 2 * qNormSq ψ := by
  classical
  rw [qNormSq_def, qNormSq_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  simp [Complex.normSq_ofReal, sq]

/-! ## The bridge -/

section

variable (Γ : Matrix X X ℝ) (u v : X → (H → ℂ))

/-- The real parts of `u` at a fixed basis vector, as a real vector indexed by
the promise domain. -/
private def reAt (u : X → (H → ℂ)) (h : H) : X → ℝ := fun x => (u x h).re

private def imAt (u : X → (H → ℂ)) (h : H) : X → ℝ := fun x => (u x h).im

omit [DecidableEq H] [DecidableEq X] in
private lemma sum_gram_re_eq (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) :
    (∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re)
      = ∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)) := by
  classical
  have hexp : ∀ x y, Γ x y * (qInner (u x) (v y)).re
      = ∑ h, (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) := by
    intro x y
    rw [qInner_re, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [reAt, imAt]
    ring
  calc (∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re)
      = ∑ x, ∑ y, ∑ h,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) := by
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hexp x y
    _ = ∑ x, ∑ h, ∑ y,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ h, ∑ x, ∑ y,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) :=
        Finset.sum_comm
    _ = ∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib

omit [DecidableEq H] [DecidableEq X] in
private lemma sum_reAt_imAt (u : X → (H → ℂ)) :
    (∑ h, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h)))
      = ∑ x, qNormSq (u x) := by
  classical
  have h1 : ∀ h : H, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
      = ∑ x, ((u x h).re * (u x h).re + (u x h).im * (u x h).im) := by
    intro h
    simp only [dotProduct, reAt, imAt]
    exact Finset.sum_add_distrib.symm
  rw [Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) => h1 h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (qNormSq_eq_sum_re_im (u x)).symm

/-- Cauchy–Schwarz in two terms, in the square-root form used twice below. -/
private lemma sqrt_mul_add_sqrt_mul_le {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt A * Real.sqrt B + Real.sqrt C * Real.sqrt D
      ≤ Real.sqrt (A + C) * Real.sqrt (B + D) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := ![A, C]) (g := ![B, D]) Finset.univ
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

omit [DecidableEq H] in
/-- **The bridge.**  A real matrix contracted against complex vector families is
bounded by its operator norm times the two total squared norms. -/
theorem abs_sum_gram_re_le :
    |∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) := by
  classical
  have hnn : ∀ (w : X → (H → ℂ)) (h : H), 0 ≤ (reAt w h) ⬝ᵥ (reAt w h) :=
    fun w h => dotProduct_self_nonneg _
  have hnn' : ∀ (w : X → (H → ℂ)) (h : H), 0 ≤ (imAt w h) ⬝ᵥ (imAt w h) :=
    fun w h => dotProduct_self_nonneg _
  -- at each basis vector, the real and imaginary bilinear forms
  have hstep : ∀ h : H,
      |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)|
        ≤ ‖Γ‖ * (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
            * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) := by
    intro h
    have h1 := abs_dotProduct_mulVec_le Γ (reAt u h) (reAt v h)
    have h2 := abs_dotProduct_mulVec_le Γ (imAt u h) (imAt v h)
    have h3 := sqrt_mul_add_sqrt_mul_le (hnn u h) (hnn v h) (hnn' u h) (hnn' v h)
    have h4 : |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)|
        ≤ ‖Γ‖ * Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h)) * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h))
          + ‖Γ‖ * Real.sqrt ((imAt u h) ⬝ᵥ (imAt u h))
            * Real.sqrt ((imAt v h) ⬝ᵥ (imAt v h)) :=
      (abs_add_le _ _).trans (add_le_add h1 h2)
    have hΓ : 0 ≤ ‖Γ‖ := norm_nonneg _
    nlinarith [h3, h4, hΓ]
  -- sum over the basis
  calc |∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re|
      = |∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h))| := by
        rw [sum_gram_re_eq]
    _ ≤ ∑ h, |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, ‖Γ‖ * (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
          * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) :=
        Finset.sum_le_sum fun h _ => hstep h
    _ = ‖Γ‖ * ∑ h, (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
          * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) := by
        rw [Finset.mul_sum]
    _ ≤ ‖Γ‖ * (Real.sqrt (∑ h, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h)))
          * Real.sqrt (∑ h, ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Real.sum_sqrt_mul_sqrt_le _
          (fun h => add_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))
          (fun h => add_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))
    _ = ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) := by
        rw [sum_reAt_imAt, sum_reAt_imAt, mul_assoc]

end

end QuantumQueryComplexity

end SourceQuantumLowerBoundBridge

section SourceQuantumLowerBoundProgress

/-!
# The adversary progress measure

For an adversary matrix `Γ`, a weight vector `δ`, and a family of states `ψ x`
indexed by the promise domain, the **progress** is

  `progress Γ δ δ' ψ = ∑ x, ∑ y, Γ x y · Re ⟪δ x • ψ x, δ' y • ψ y⟫`.

The two weight vectors are **not** a generalization for its own sake: they are
what lets the endgame use the bilinear characterization of the operator norm
(`l2_opNorm_le_of_forall_dotProduct`, already in `SourceSpectral`) instead of a
norm-attaining eigenvector, which the project does not have and which would
need the spectral theorem.

Three facts drive the lower bound, and they are the three theorems here:

* `progress_mulVec` — an **input-independent** unitary does not change it.  This
  is why only queries can make progress.
* `progress_const` — at time zero all the states coincide, so the progress is
  `δ ⬝ᵥ Γ *ᵥ δ'`, which the bilinear characterization can make as close to
  `‖Γ‖` as one likes.
* `abs_progress_oracle_sub_le` — **one query changes it by at most
  `2c √(∑ δ²) √(∑ δ'²)`**, where `c` bounds every `‖Γ ⊙ advDOn read i‖`.

The query step is where the model meets the adversary matrix.  Decompose a state
by its query-index register, `ψ = ∑_o qRestrict idxOf o ψ` over `o : Option ι`.
The oracle preserves each sector, acts as the identity on the idle sector
`none`, and on the sector `some i` depends on the input only through its `i`-th
letter.  So a pair `x, y` contributes to the *change* only through sectors `i`
with `read x i ≠ read y i` — precisely the support of the mask `advDOn read i`.
Replacing `Γ` by `Γ ⊙ advDOn read i` on the sector `i` is therefore free, and
the bridge bounds each of the two resulting Gram forms by `‖Γ ⊙ advDOn read i‖`
times that sector's weight.  Summing over sectors needs only that the sector
weights add up to the total, plus one Cauchy–Schwarz over the sectors.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The Gram form -/

/-- A real matrix contracted against two families of complex vectors. -/
noncomputable def gramForm (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) : ℝ :=
  ∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re

omit [DecidableEq H] in
/-- The bridge, in `gramForm` notation. -/
lemma abs_gramForm_le (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) :
    |gramForm Γ u v|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) := by
  classical
  exact abs_sum_gram_re_le Γ u v

omit [DecidableEq H] in
/-- The self-paired case, where the two square roots collapse. -/
lemma abs_gramForm_self_le (Γ : Matrix X X ℝ) (u : X → (H → ℂ)) :
    |gramForm Γ u u| ≤ ‖Γ‖ * ∑ x, qNormSq (u x) := by
  classical
  have h := abs_gramForm_le Γ u u
  have hnn : 0 ≤ ∑ x, qNormSq (u x) :=
    Finset.sum_nonneg fun x _ => qNormSq_nonneg _
  rwa [mul_assoc, Real.mul_self_sqrt hnn] at h

omit [DecidableEq H] [DecidableEq X] in
lemma gramForm_add_left (Γ : Matrix X X ℝ) (u u' v : X → (H → ℂ)) :
    gramForm Γ (fun x => u x + u' x) v = gramForm Γ u v + gramForm Γ u' v := by
  classical
  simp only [gramForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [qInner_add_left, Complex.add_re, mul_add]

omit [DecidableEq H] [DecidableEq X] in
lemma gramForm_add_right (Γ : Matrix X X ℝ) (u v v' : X → (H → ℂ)) :
    gramForm Γ u (fun y => v y + v' y) = gramForm Γ u v + gramForm Γ u v' := by
  classical
  simp only [gramForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [qInner_add_right, Complex.add_re, mul_add]

omit [DecidableEq H] [DecidableEq X] in
/-- **Masking is free** when the masked-out pairs contribute equally to both
Gram forms. -/
lemma gramForm_sub_eq_mask {Γ M : Matrix X X ℝ} {p : X → X → Prop} [DecidableRel p]
    {u v u' v' : X → (H → ℂ)}
    (hM : ∀ x y, M x y = if p x y then 0 else Γ x y)
    (hzero : ∀ x y, p x y →
      (qInner (u x) (v y)).re = (qInner (u' x) (v' y)).re) :
    gramForm Γ u v - gramForm Γ u' v' = gramForm M u v - gramForm M u' v' := by
  simp only [gramForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hM]
  by_cases h : p x y
  · rw [ite_eq_left h, hzero x y h]
    ring
  · rw [ite_eq_right h]

/-! ## Sector decomposition by the query-index register -/

/-- The query-index register, used as a readout map. -/
@[expose]
def idxOf : QBasis ι σ W → Option ι := fun p => p.1

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma idxOf_apply (p : QBasis ι σ W) : idxOf p = p.1 := rfl

omit [DecidableEq W] [DecidableEq X] [DecidableEq σ] in
/-- The Gram form decomposes over the sectors. -/
lemma gramForm_eq_sum_sector (Γ : Matrix X X ℝ) (u v : X → (QBasis ι σ W → ℂ)) :
    gramForm Γ u v = ∑ o : Option ι,
      gramForm Γ (fun x => qRestrict idxOf o (u x))
        (fun y => qRestrict idxOf o (v y)) := by
  classical
  have hre : ∀ x y, Γ x y * (qInner (u x) (v y)).re
      = ∑ o : Option ι,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re := by
    intro x y
    rw [qInner_eq_sum_qRestrict idxOf, Complex.re_sum, Finset.mul_sum]
  calc gramForm Γ u v
      = ∑ x, ∑ y, ∑ o : Option ι,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hre x y
    _ = ∑ x, ∑ o : Option ι, ∑ y,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ o : Option ι, ∑ x, ∑ y,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_comm

/-! ## How the oracle acts on the sectors -/

/-- The oracle preserves each sector. -/
lemma qRestrict_idxOf_oracleMat (a : ι → σ) (o : Option ι) (ψ : QBasis ι σ W → ℂ) :
    qRestrict idxOf o (oracleMat a *ᵥ ψ) = oracleMat a *ᵥ (qRestrict idxOf o ψ) := by
  funext p
  rw [qRestrict, oracleMat_mulVec_apply, oracleMat_mulVec_apply, qRestrict,
    idxOf_apply, idxOf_apply, oracleMap_fst]

/-- On the idle sector the oracle is the identity. -/
lemma oracleMat_mulVec_qRestrict_none (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ (qRestrict idxOf none ψ) = qRestrict idxOf none ψ := by
  funext p
  rw [oracleMat_mulVec_apply, qRestrict, qRestrict, idxOf_apply, idxOf_apply,
    oracleMap_fst]
  obtain ⟨(_ | i), t, w⟩ := p
  · rw [ite_eq_left rfl, ite_eq_left rfl, oracleMap_none]
  · rw [ite_eq_right (by simp), ite_eq_right (by simp)]

/-- On the sector `some i` the oracle depends on the input only through its
`i`-th letter. -/
lemma oracleMat_mulVec_qRestrict_some {a b : ι → σ} {i : ι} (hab : a i = b i)
    (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ (qRestrict idxOf (some i) ψ)
      = oracleMat b *ᵥ (qRestrict idxOf (some i) ψ) := by
  funext p
  rw [oracleMat_mulVec_apply, oracleMat_mulVec_apply, qRestrict, qRestrict,
    idxOf_apply, idxOf_apply, oracleMap_fst, oracleMap_fst]
  by_cases hp : p.1 = some i
  · rw [ite_eq_left hp, ite_eq_left hp]
    obtain ⟨k, t, w⟩ := p
    simp only at hp
    subst hp
    rw [oracleMap_some, oracleMap_some, hab]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-! ## The progress measure -/

/-- The weighted family `x ↦ δ x • ψ x`. -/
@[expose]
noncomputable def qScale (δ : X → ℝ) (ψ : X → (H → ℂ)) : X → (H → ℂ) :=
  fun x => (δ x : ℂ) • ψ x

omit [DecidableEq H] [DecidableEq X] [Fintype H] [Fintype X] in
lemma qScale_apply (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qScale δ ψ x = (δ x : ℂ) • ψ x := rfl

omit [DecidableEq H] [DecidableEq X] [Fintype X] in
lemma qNormSq_qScale (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qNormSq (qScale δ ψ x) = δ x ^ 2 * qNormSq (ψ x) := by
  classical
  exact qNormSq_real_smul _ _

omit [DecidableEq H] [DecidableEq X] [Fintype H] [Fintype X] in
lemma qScale_add (δ : X → ℝ) (u v : X → (H → ℂ)) (x : X) :
    qScale δ (fun x => u x + v x) x = qScale δ u x + qScale δ v x := by
  rw [qScale_apply, qScale_apply, qScale_apply, smul_add]

omit [DecidableEq H] [DecidableEq X] [Fintype X] in
lemma qScale_mulVec (U : Matrix H H ℂ) (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qScale δ (fun x => U *ᵥ ψ x) x = U *ᵥ (qScale δ ψ x) := by
  rw [qScale_apply, qScale_apply, Matrix.mulVec_smul]

/-- **The progress measure.** -/
noncomputable def progress (Γ : Matrix X X ℝ) (δ δ' : X → ℝ)
    (ψ : X → (H → ℂ)) : ℝ :=
  gramForm Γ (qScale δ ψ) (qScale δ' ψ)

omit [DecidableEq H] in
/-- The master bound on the progress. -/
lemma abs_progress_le (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (ψ : X → (H → ℂ)) :
    |progress Γ δ δ' ψ|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y)) := by
  classical
  have h := abs_gramForm_le Γ (qScale δ ψ) (qScale δ' ψ)
  rwa [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => qNormSq_qScale δ ψ x,
    Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => qNormSq_qScale δ' ψ y] at h

omit [DecidableEq X] in
/-- **An input-independent unitary does not change the progress.** -/
theorem progress_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (ψ : X → (H → ℂ)) :
    progress Γ δ δ' (fun x => U *ᵥ ψ x) = progress Γ δ δ' ψ := by
  classical
  simp only [progress, gramForm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [qScale_mulVec, qScale_mulVec, qInner_mulVec_mulVec hU]

omit [DecidableEq H] [DecidableEq X] in
/-- **At time zero the progress is `δ ⬝ᵥ Γ *ᵥ δ'`.** -/
theorem progress_const (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) {ψ₀ : H → ℂ}
    (hψ : IsQState ψ₀) : progress Γ δ δ' (fun _ => ψ₀) = δ ⬝ᵥ Γ *ᵥ δ' := by
  classical
  have hval : ∀ x y : X,
      Γ x y * (qInner (qScale δ (fun _ => ψ₀) x) (qScale δ' (fun _ => ψ₀) y)).re
        = δ x * Γ x y * δ' y := by
    intro x y
    have h1 : qInner (qScale δ (fun _ => ψ₀) x) (qScale δ' (fun _ => ψ₀) y)
        = ((δ x * δ' y : ℝ) : ℂ) := by
      rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right,
        qInner_self, hψ]
      push_cast
      rw [RCLike.star_def, Complex.conj_ofReal]
      ring
    rw [h1, Complex.ofReal_re]
    ring
  rw [dotProduct_mulVec_eq_sum]
  simp only [progress, gramForm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hval x y

/-! ## The query step -/

section Query

variable (read : X → ι → σ) (Γ : Matrix X X ℝ) (δ : X → ℝ)
  (ψ : X → (QBasis ι σ W → ℂ))

/-- The weighted family restricted to the sector `o`. -/
@[expose]
noncomputable def sectFam (o : Option ι) (δ : X → ℝ)
    (ψ : X → (QBasis ι σ W → ℂ)) : X → (QBasis ι σ W → ℂ) :=
  fun x => (δ x : ℂ) • qRestrict idxOf o (ψ x)

omit [DecidableEq W] [DecidableEq X] [DecidableEq σ] [Fintype W] [Fintype X] [Fintype ι]
    [Fintype σ] in
lemma sectFam_apply (o : Option ι) (x : X) :
    sectFam o δ ψ x = (δ x : ℂ) • qRestrict idxOf o (ψ x) := rfl

omit [DecidableEq W] [DecidableEq X] [DecidableEq σ] [Fintype W] [Fintype X] [Fintype ι]
    [Fintype σ] in
lemma qScale_restrict_eq_sectFam (o : Option ι) (x : X) :
    qRestrict idxOf o (qScale δ ψ x) = sectFam o δ ψ x := by
  classical
  funext p
  rw [qRestrict, qScale_apply, sectFam_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, qRestrict]
  by_cases hp : idxOf p = o
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, mul_zero]

omit [DecidableEq X] [Fintype X] in
/-- The oracle acts on the sector families through the state family. -/
lemma sectFam_oracle (o : Option ι) (x : X) :
    sectFam o δ (fun x => oracleMat (read x) *ᵥ ψ x) x
      = oracleMat (read x) *ᵥ sectFam o δ ψ x := by
  classical
  rw [sectFam_apply, sectFam_apply, qRestrict_idxOf_oracleMat, Matrix.mulVec_smul]

/-- The weight carried by the sector `o`. -/
noncomputable def sectorWeight (δ : X → ℝ) (ψ : X → (QBasis ι σ W → ℂ))
    (o : Option ι) : ℝ :=
  ∑ x, qNormSq (sectFam o δ ψ x)

omit [DecidableEq W] [DecidableEq X] [DecidableEq σ] in
lemma sectorWeight_nonneg (o : Option ι) : 0 ≤ sectorWeight δ ψ o := by
  classical
  exact Finset.sum_nonneg fun _ _ => qNormSq_nonneg _

omit [DecidableEq W] [DecidableEq X] [DecidableEq σ] in
/-- The sector weights sum to the total weight. -/
lemma sum_sectorWeight :
    ∑ o : Option ι, sectorWeight δ ψ o = ∑ x, δ x ^ 2 * qNormSq (ψ x) := by
  classical
  calc ∑ o : Option ι, sectorWeight δ ψ o
      = ∑ o : Option ι, ∑ x, δ x ^ 2 * qNormSq (qRestrict idxOf o (ψ x)) := by
        refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun x _ => ?_
        rw [sectFam_apply, qNormSq_real_smul]
    _ = ∑ x, ∑ o : Option ι, δ x ^ 2 * qNormSq (qRestrict idxOf o (ψ x)) :=
        Finset.sum_comm
    _ = ∑ x, δ x ^ 2 * qNormSq (ψ x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [← sum_qProb (idxOf (ι := ι) (σ := σ) (W := W)) (ψ x)]
        exact Finset.sum_congr rfl fun o _ => (qProb_eq_qNormSq_qRestrict _ _ _).symm

/-- **One query changes the progress by at most `2c` times the two weights.** -/
theorem abs_progress_oracle_sub_le (δ' : X → ℝ) {c : ℝ}
    (hc : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ c) (hc0 : 0 ≤ c) :
    |progress Γ δ δ' (fun x => oracleMat (read x) *ᵥ ψ x) - progress Γ δ δ' ψ|
      ≤ 2 * c * (Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y))) := by
  classical
  set ψ' : X → (QBasis ι σ W → ℂ) := fun x => oracleMat (read x) *ᵥ ψ x with hψ'
  -- the oracle is unitary, so it does not change any sector weight
  have hweight : ∀ (e : X → ℝ) (o : Option ι),
      ∑ x, qNormSq (sectFam o e ψ' x) = sectorWeight e ψ o := by
    intro e o
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hψ', sectFam_oracle, qNormSq_mulVec (oracleMat_mem_unitaryGroup _)]
  -- both progresses, decomposed over sectors
  have hdecomp : progress Γ δ δ' ψ' - progress Γ δ δ' ψ
      = ∑ o : Option ι,
          (gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)) := by
    rw [progress, progress, gramForm_eq_sum_sector, gramForm_eq_sum_sector,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [funext fun x => qScale_restrict_eq_sectFam δ ψ o x,
      funext fun x => qScale_restrict_eq_sectFam δ' ψ o x,
      funext fun x => qScale_restrict_eq_sectFam δ ψ' o x,
      funext fun x => qScale_restrict_eq_sectFam δ' ψ' o x]
  -- each sector's contribution
  have hsector : ∀ o : Option ι,
      |gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
        - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)|
        ≤ 2 * c * (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) := by
    intro o
    have hw := sectorWeight_nonneg δ ψ o
    have hw' := sectorWeight_nonneg δ' ψ o
    have hprod : 0 ≤ Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    cases o with
    | none =>
        -- the oracle acts trivially on the idle sector
        have hfam : ∀ e : X → ℝ, sectFam none e ψ' = sectFam none e ψ := by
          intro e
          funext x
          rw [hψ', sectFam_oracle, sectFam_apply, Matrix.mulVec_smul,
            oracleMat_mulVec_qRestrict_none]
        rw [hfam δ, hfam δ', sub_self, abs_zero]
        have : (0 : ℝ) ≤ 2 * c := by linarith
        exact mul_nonneg this hprod
    | some i =>
        -- pairs agreeing at `i` contribute equally, so the mask is free
        have hmask : gramForm Γ (sectFam (some i) δ ψ') (sectFam (some i) δ' ψ')
            - gramForm Γ (sectFam (some i) δ ψ) (sectFam (some i) δ' ψ)
            = gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
                (sectFam (some i) δ' ψ')
              - gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ)
                (sectFam (some i) δ' ψ) := by
          refine gramForm_sub_eq_mask (p := fun x y => read x i = read y i)
            (fun x y => hadamard_advDOn_apply read Γ i x y) ?_
          intro x y hagree
          have hxy : oracleMat (read y) *ᵥ sectFam (some i) δ' ψ y
              = oracleMat (read x) *ᵥ sectFam (some i) δ' ψ y := by
            rw [sectFam_apply, Matrix.mulVec_smul, Matrix.mulVec_smul,
              oracleMat_mulVec_qRestrict_some hagree.symm]
          congr 1
          rw [sectFam_oracle, sectFam_oracle, hxy,
            qInner_mulVec_mulVec (oracleMat_mem_unitaryGroup _)]
        rw [hmask]
        have h1 := abs_gramForm_le (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
          (sectFam (some i) δ' ψ')
        have h2 := abs_gramForm_le (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ)
          (sectFam (some i) δ' ψ)
        rw [hweight δ (some i), hweight δ' (some i)] at h1
        rw [show (∑ x, qNormSq (sectFam (some i) δ ψ x)) = sectorWeight δ ψ (some i) from rfl,
          show (∑ y, qNormSq (sectFam (some i) δ' ψ y)) = sectorWeight δ' ψ (some i) from rfl]
          at h2
        have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
          intro a b
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
        have hmul : ‖Γ ⊙ advDOn read i‖
              * Real.sqrt (sectorWeight δ ψ (some i))
              * Real.sqrt (sectorWeight δ' ψ (some i))
            ≤ c * (Real.sqrt (sectorWeight δ ψ (some i))
              * Real.sqrt (sectorWeight δ' ψ (some i))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hc i) hprod
        have := htri (gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
            (sectFam (some i) δ' ψ'))
          (gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ) (sectFam (some i) δ' ψ))
        linarith
  calc |progress Γ δ δ' ψ' - progress Γ δ δ' ψ|
      = |∑ o : Option ι, (gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ))| := by rw [hdecomp]
    _ ≤ ∑ o : Option ι, |gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o : Option ι, 2 * c *
          (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) :=
        Finset.sum_le_sum fun o _ => hsector o
    _ = 2 * c * ∑ o : Option ι,
          (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * c * (Real.sqrt (∑ o : Option ι, sectorWeight δ ψ o)
          * Real.sqrt (∑ o : Option ι, sectorWeight δ' ψ o)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.sum_sqrt_mul_sqrt_le _ (fun o => sectorWeight_nonneg δ ψ o)
          (fun o => sectorWeight_nonneg δ' ψ o)
    _ = 2 * c * (Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y))) := by
        rw [sum_sectorWeight, sum_sectorWeight]

end Query

end QuantumQueryComplexity

end SourceQuantumLowerBoundProgress

section SourceQuantumLowerBoundOutput

/-!
# The output condition

At the end of a successful computation the progress must be *small*: an
adversary matrix is supported on pairs with different `f`-values, and a state
that announces `f x` with probability at least `1 - ε` is nearly orthogonal to
one that announces `f y ≠ f x`.

Split each final state along the outcome it is supposed to announce,

  `ψ x = A x + B x`,  `A x = qRestrict readout (f x) (ψ x)`,

so `‖A x‖² ≥ 1 - ε` and `‖B x‖² ≤ ε`.  The `A`–`A` term of the expanded Gram
form vanishes **entirely**: where `Γ` is nonzero the two outcomes differ, and
distinct outcomes are orthogonal (`qInner_qRestrict_of_ne`); where the outcomes
agree `Γ` is zero.  The remaining three terms are bounded by the bridge, giving

  `|progress| ≤ ‖Γ‖ (2√ε + ε)`.

**On the constant.**  The sharp bound for this step is `2√(ε(1-ε))`, which is
what makes `ε = 1/3` work in the literature.  For general finite outputs the
matrix-level argument here gives `2√ε + ε` instead, which is `< 1` exactly
when `ε < 3 - 2√2 ≈ 0.1716`.  For **Boolean** outputs the sharp constant IS
recovered directly — `SourceQuantumLowerBoundOutputBool` (the error parts are orthogonal on the
adversary matrix's support, and the masses are linked), consumed by
`SourceQuantumLowerBoundMainBool` for the `ε = 1/3` lower bound.  Amplification remains the
relevant route only for general outputs, where the `B`–`B` term does not
vanish.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {O : Type} [DecidableEq O]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {H : Type} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- **The output condition.**  On final states that are correct with probability
at least `1 - ε`, the progress of any adversary matrix is at most
`‖Γ‖ (2√ε + ε)`. -/
theorem abs_progress_output_le {Γ : Matrix X X ℝ} {f : X → O}
    (hΓ : ∀ x y, f x = f y → Γ x y = 0)
    {ψ : X → (H → ℂ)} (hψ : ∀ x, IsQState (ψ x))
    {p : H → O} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hp : ∀ x, 1 - ε ≤ qProb p (ψ x) (f x))
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |progress Γ δ δ' ψ| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by
  classical
  set A : X → (H → ℂ) := fun x => qRestrict p (f x) (ψ x) with hA
  set B : X → (H → ℂ) := fun x => ψ x - A x with hB
  have hsplit : ∀ x, ψ x = A x + B x := by
    intro x
    rw [hB]
    simp
  -- the four norms
  have hnormA : ∀ x, qNormSq (A x) = qProb p (ψ x) (f x) := by
    intro x
    rw [hA, qProb_eq_qNormSq_qRestrict]
  have hnormB : ∀ x, qNormSq (B x) = 1 - qProb p (ψ x) (f x) := by
    intro x
    rw [hB, hA, qNormSq_sub_qRestrict, hψ x]
  have hsumA : ∑ x, qNormSq (qScale δ A x) ≤ 1 := by
    calc ∑ x, qNormSq (qScale δ A x) = ∑ x, δ x ^ 2 * qProb p (ψ x) (f x) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormA x]
      _ ≤ ∑ x, δ x ^ 2 * 1 :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (qProb_le_one (hψ x) p (f x)) (sq_nonneg _)
      _ = 1 := by simpa using hδ
  have hsumA' : ∑ y, qNormSq (qScale δ' A y) ≤ 1 := by
    calc ∑ y, qNormSq (qScale δ' A y) = ∑ y, δ' y ^ 2 * qProb p (ψ y) (f y) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormA y]
      _ ≤ ∑ y, δ' y ^ 2 * 1 :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (qProb_le_one (hψ y) p (f y)) (sq_nonneg _)
      _ = 1 := by simpa using hδ'
  have hsumB : ∑ x, qNormSq (qScale δ B x) ≤ ε := by
    calc ∑ x, qNormSq (qScale δ B x) = ∑ x, δ x ^ 2 * (1 - qProb p (ψ x) (f x)) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormB x]
      _ ≤ ∑ x, δ x ^ 2 * ε :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp x]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ, one_mul]
  have hsumB' : ∑ y, qNormSq (qScale δ' B y) ≤ ε := by
    calc ∑ y, qNormSq (qScale δ' B y) = ∑ y, δ' y ^ 2 * (1 - qProb p (ψ y) (f y)) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormB y]
      _ ≤ ∑ y, δ' y ^ 2 * ε :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp y]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ', one_mul]
  -- the `A`–`A` term vanishes
  have hAA : gramForm Γ (qScale δ A) (qScale δ' A) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have : qInner (qScale δ A x) (qScale δ' A y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right, hA]
        rw [qInner_qRestrict_of_ne p hf]
        ring
      rw [this]
      simp
  -- expand and bound the three remaining terms
  have hexp : progress Γ δ δ' ψ
      = gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)
        + gramForm Γ (qScale δ B) (qScale δ' B) := by
    have h1 : qScale δ ψ = fun x => qScale δ A x + qScale δ B x := by
      funext x
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ w x) (funext hsplit)
    have h2 : qScale δ' ψ = fun y => qScale δ' A y + qScale δ' B y := by
      funext y
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ' w y) (funext hsplit)
    rw [progress, h1, h2, gramForm_add_left, gramForm_add_right, gramForm_add_right,
      hAA]
    ring
  have hb1 := abs_gramForm_le Γ (qScale δ A) (qScale δ' B)
  have hb2 := abs_gramForm_le Γ (qScale δ B) (qScale δ' A)
  have hb3 := abs_gramForm_le Γ (qScale δ B) (qScale δ' B)
  have hsqA : Real.sqrt (∑ x, qNormSq (qScale δ A x)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hsumA
  have hsqA' : Real.sqrt (∑ y, qNormSq (qScale δ' A y)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hsumA'
  have hsqB : Real.sqrt (∑ x, qNormSq (qScale δ B x)) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hsumB
  have hsqB' : Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hsumB'
  have hΓ0 : (0 : ℝ) ≤ ‖Γ‖ := norm_nonneg _
  have hεs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hεsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0
  have hb1' : |gramForm Γ (qScale δ A) (qScale δ' B)| ≤ ‖Γ‖ * Real.sqrt ε := by
    refine hb1.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ A x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ 1 * Real.sqrt ε :=
      mul_le_mul hsqA hsqB' (Real.sqrt_nonneg _) zero_le_one
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ A x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' B y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ A x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' B y))) := by ring
      _ ≤ ‖Γ‖ * (1 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * Real.sqrt ε := by ring
  have hb2' : |gramForm Γ (qScale δ B) (qScale δ' A)| ≤ ‖Γ‖ * Real.sqrt ε := by
    refine hb2.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ B x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' A y)) ≤ Real.sqrt ε * 1 :=
      mul_le_mul hsqB hsqA' (Real.sqrt_nonneg _) hεs
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ B x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' A y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ B x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' A y))) := by ring
      _ ≤ ‖Γ‖ * (Real.sqrt ε * 1) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * Real.sqrt ε := by ring
  have hb3' : |gramForm Γ (qScale δ B) (qScale δ' B)| ≤ ‖Γ‖ * ε := by
    refine hb3.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ B x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ Real.sqrt ε * Real.sqrt ε :=
      mul_le_mul hsqB hsqB' (Real.sqrt_nonneg _) hεs
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ B x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' B y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ B x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' B y))) := by ring
      _ ≤ ‖Γ‖ * (Real.sqrt ε * Real.sqrt ε) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * ε := by rw [hεsq]
  rw [hexp]
  calc |gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)
        + gramForm Γ (qScale δ B) (qScale δ' B)|
      ≤ |gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)|
          + |gramForm Γ (qScale δ B) (qScale δ' B)| := abs_add_le _ _
    _ ≤ (|gramForm Γ (qScale δ A) (qScale δ' B)| + |gramForm Γ (qScale δ B) (qScale δ' A)|)
          + |gramForm Γ (qScale δ B) (qScale δ' B)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by linarith

end QuantumQueryComplexity

end SourceQuantumLowerBoundOutput

section SourceQuantumLowerBoundMain

/-!
# The adversary lower bound

Every quantum algorithm that computes `f` on the promise
`read` with error at most `ε` makes at least

  `(1 - (2√ε + ε)) / 2 · advPMOn read f`

queries.  The three ingredients are the ones proved in `SourceQuantumLowerBoundProgress` and
`SourceQuantumLowerBoundOutput`: the progress starts at `δ ⬝ᵥ Γ *ᵥ δ'`, moves by at most `2` per
query, and ends below `‖Γ‖ (2√ε + ε)`.

**Why two weight vectors.**  The classical proof takes `δ` to be a
norm-attaining eigenvector of `Γ`, so that the initial progress *is* `‖Γ‖`.
That needs the spectral theorem for real symmetric matrices, which this project
has deliberately avoided.  Carrying two weight vectors instead makes the initial
progress the **bilinear** form `δ ⬝ᵥ Γ *ᵥ δ'`, and `SourceSpectral`'s
`l2_opNorm_le_of_forall_dotProduct` — already proved, and used throughout the
adversary side — converts a bound on all of those into a bound on `‖Γ‖`.  The
only extra work is normalizing an arbitrary pair of vectors, which is four
lines.

The error threshold is `2√ε + ε < 1`, i.e. `ε < 3 - 2√2 ≈ 0.1716`; see
`SourceQuantumLowerBoundOutput` for why this is not the sharp `2√(ε(1-ε))` and what recovers the
conventional `ε = 1/3`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The progress of an algorithm -/

/-- The progress carried by an algorithm's states after `t` queries. -/
noncomputable def algProgress (Γ : Matrix X X ℝ) (δ δ' : X → ℝ)
    (A : QAlg ι σ O W) (read : X → ι → σ) (t : ℕ) : ℝ :=
  progress Γ δ δ' (fun x => A.state (read x) t)

omit [DecidableEq O] [DecidableEq X] in
/-- **Before any query the progress is the bilinear form.** -/
lemma algProgress_zero (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (A : QAlg ι σ O W)
    (read : X → ι → σ) : algProgress Γ δ δ' A read 0 = δ ⬝ᵥ Γ *ᵥ δ' := by
  classical
  rw [algProgress, show (fun x => A.state (read x) 0) = fun _ => A.step 0 *ᵥ A.init from rfl]
  exact progress_const Γ δ δ'
    (IsQState.mulVec (A.step_unitary 0) A.init_isQState)

omit [DecidableEq O] in
/-- **One query moves the progress by at most `2`.** -/
lemma abs_algProgress_succ_sub_le {Γ : Matrix X X ℝ} {δ δ' : X → ℝ}
    (A : QAlg ι σ O W) {read : X → ι → σ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) (t : ℕ) :
    |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read t| ≤ 2 := by
  have hstep : (fun x => A.state (read x) (t + 1))
      = fun x => A.step (t + 1) *ᵥ (oracleMat (read x) *ᵥ A.state (read x) t) := rfl
  rw [algProgress, algProgress, hstep, progress_mulVec (A.step_unitary (t + 1))]
  have h := abs_progress_oracle_sub_le read Γ δ (fun x => A.state (read x) t) δ'
    hfeas zero_le_one
  have hw : ∑ x, δ x ^ 2 * qNormSq (A.state (read x) t) = 1 := by
    rw [← hδ]
    exact Finset.sum_congr rfl fun x _ => by rw [A.state_isQState (read x) t, mul_one]
  have hw' : ∑ y, δ' y ^ 2 * qNormSq (A.state (read y) t) = 1 := by
    rw [← hδ']
    exact Finset.sum_congr rfl fun y _ => by rw [A.state_isQState (read y) t, mul_one]
  rw [hw, hw', Real.sqrt_one, mul_one, mul_one] at h
  linarith

omit [DecidableEq O] in
/-- **After `q` queries the progress has moved by at most `2q`.** -/
lemma abs_algProgress_sub_zero_le {Γ : Matrix X X ℝ} {δ δ' : X → ℝ}
    (A : QAlg ι σ O W) {read : X → ι → σ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) (q : ℕ) :
    |algProgress Γ δ δ' A read q - algProgress Γ δ δ' A read 0| ≤ 2 * q := by
  classical
  induction q with
  | zero => simp
  | succ t ih =>
      have h1 := abs_algProgress_succ_sub_le A hfeas hδ hδ' t
      have h2 : |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read 0|
          ≤ |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read t|
            + |algProgress Γ δ δ' A read t - algProgress Γ δ δ' A read 0| :=
        abs_sub_le _ _ _
      push_cast
      linarith

/-! ## The lower bound -/

section

variable {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {f : X → O} {ε : ℝ}

omit [DecidableEq O] in
/-- **The telescoping step, parametric in the output constant**: any bound
`‖Γ‖·κ` on the progress after `q` queries bounds the initial bilinear form by
`‖Γ‖·κ + 2q`. -/
lemma abs_dotProduct_mulVec_le_of_algProgress {Γ : Matrix X X ℝ} {κ : ℝ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1)
    (hout : |algProgress Γ δ δ' A read q| ≤ ‖Γ‖ * κ) :
    |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * κ + 2 * q := by
  classical
  have htel := abs_algProgress_sub_zero_le A hfeas hδ hδ' q
  have h0 := algProgress_zero Γ δ δ' A read
  have hsplit : |algProgress Γ δ δ' A read 0|
      ≤ |algProgress Γ δ δ' A read q|
        + |algProgress Γ δ δ' A read q - algProgress Γ δ δ' A read 0| := by
    have := abs_sub_le (algProgress Γ δ δ' A read 0) (algProgress Γ δ δ' A read q) 0
    simp only [sub_zero] at this
    rw [abs_sub_comm (algProgress Γ δ δ' A read 0)] at this
    linarith
  rw [h0] at hsplit htel
  linarith

/-- The bilinear form of any feasible adversary matrix is bounded by the
algorithm's query count and error. -/
lemma abs_dotProduct_mulVec_le_of_computes {Γ : Matrix X X ℝ}
    (hΓ : IsAdvMatrixOn f Γ) (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hcomp : ComputesWithErrorOn A q read f ε)
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) + 2 * q := by
  classical
  have hout : |algProgress Γ δ δ' A read q| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by
    rw [algProgress]
    exact abs_progress_output_le (fun x y h => hΓ.2 x y h)
      (fun x => A.state_isQState (read x) q) hε0 (fun x => hcomp x) hδ hδ'
  exact abs_dotProduct_mulVec_le_of_algProgress hfeas hδ hδ' hout

omit [DecidableEq O] [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- **The endgame, parametric in the output constant.**  If every feasible
adversary matrix satisfies the bilinear bound `‖Γ‖·κ + 2q` on unit weight
vectors, then `(1 − κ)·advPMOn ≤ 2q`.  Instantiated by
`advPMOn_le_of_computes` with `κ = 2√ε + ε`, and by the Boolean sharpening
(`SourceQuantumLowerBoundMainBool`) with `κ = 2√(ε(1−ε))`. -/
theorem advPMOn_le_of_bilinear {κ : ℝ} (hκ0 : 0 ≤ κ) (hlt : κ < 1)
    (hbil : ∀ Γ : Matrix X X ℝ, IsAdvMatrixOn f Γ →
      (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) →
      ∀ δ δ' : X → ℝ, (∑ x, δ x ^ 2 = 1) → (∑ y, δ' y ^ 2 = 1) →
        |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * κ + 2 * q) :
    (1 - κ) * advPMOn read f ≤ 2 * q := by
  classical
  have hpos : 0 < 1 - κ := by linarith
  rw [← le_div_iff₀' hpos]
  refine advPMOn_le fun Γ hΓ hfeas => ?_
  set K : ℝ := ‖Γ‖ * κ + 2 * q with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ ‖Γ‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ ‖Γ‖ * κ := mul_nonneg h1 hκ0
    rw [hK]
    linarith
  -- the bilinear bound, for arbitrary (not necessarily unit) vectors
  have key : ∀ a b : X → ℝ,
      |a ⬝ᵥ Γ *ᵥ b| ≤ K * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
    intro a b
    have hsum : ∀ w : X → ℝ, (∑ x, w x ^ 2) = w ⬝ᵥ w := by
      intro w
      exact Finset.sum_congr rfl fun x _ => pow_two (w x)
    rcases eq_or_lt_of_le (dotProduct_self_nonneg a) with ha | ha
    · have ha0 : a = 0 := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => mul_self_nonneg (a x))).mp ha.symm x
            (Finset.mem_univ x)
        exact mul_self_eq_zero.mp this
      rw [ha0]
      simp
    rcases eq_or_lt_of_le (dotProduct_self_nonneg b) with hb | hb
    · have hb0 : b = 0 := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => mul_self_nonneg (b x))).mp hb.symm x
            (Finset.mem_univ x)
        exact mul_self_eq_zero.mp this
      rw [hb0]
      simp
    -- normalize
    set s : ℝ := Real.sqrt (a ⬝ᵥ a) with hs
    set s' : ℝ := Real.sqrt (b ⬝ᵥ b) with hs'
    have hs0 : 0 < s := Real.sqrt_pos.mpr ha
    have hs'0 : 0 < s' := Real.sqrt_pos.mpr hb
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hs'ne : s' ≠ 0 := ne_of_gt hs'0
    have hss : s * s = a ⬝ᵥ a := Real.mul_self_sqrt (dotProduct_self_nonneg a)
    have hss' : s' * s' = b ⬝ᵥ b := Real.mul_self_sqrt (dotProduct_self_nonneg b)
    have hunit : ∑ x, (s⁻¹ * a x) ^ 2 = 1 := by
      have : ∑ x, (s⁻¹ * a x) ^ 2 = s⁻¹ ^ 2 * ∑ x, a x ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, hsum, ← hss]
      field_simp
    have hunit' : ∑ y, (s'⁻¹ * b y) ^ 2 = 1 := by
      have : ∑ y, (s'⁻¹ * b y) ^ 2 = s'⁻¹ ^ 2 * ∑ y, b y ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [this, hsum, ← hss']
      field_simp
    have hmaster := hbil Γ hΓ hfeas _ _ hunit hunit'
    have hscale : (fun x => s⁻¹ * a x) ⬝ᵥ Γ *ᵥ (fun y => s'⁻¹ * b y)
        = s⁻¹ * s'⁻¹ * (a ⬝ᵥ Γ *ᵥ b) := by
      rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hscale] at hmaster
    rw [abs_mul] at hmaster
    have habs : |s⁻¹ * s'⁻¹| = s⁻¹ * s'⁻¹ := abs_of_pos (by positivity)
    rw [habs] at hmaster
    have h2 : (0 : ℝ) < s * s' := by positivity
    calc |a ⬝ᵥ Γ *ᵥ b| = (s * s') * (s⁻¹ * s'⁻¹ * |a ⬝ᵥ Γ *ᵥ b|) := by field_simp
      _ ≤ (s * s') * K := mul_le_mul_of_nonneg_left hmaster h2.le
      _ = K * s * s' := by ring
  have hnorm := l2_opNorm_le_of_forall_dotProduct Γ hK0 key
  rw [hK] at hnorm
  rw [le_div_iff₀' hpos]
  linarith

/-- **The adversary lower bound.**  A `q`-query algorithm with error `ε` forces
`advPMOn read f ≤ 2q / (1 - (2√ε + ε))`. -/
theorem advPMOn_le_of_computes (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1)
    (hcomp : ComputesWithErrorOn A q read f ε) :
    (1 - (2 * Real.sqrt ε + ε)) * advPMOn read f ≤ 2 * q := by
  classical
  exact advPMOn_le_of_bilinear
      (add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg ε)) hε0) hlt
      (fun Γ hΓ hfeas δ δ' hδ hδ' =>
        abs_dotProduct_mulVec_le_of_computes hΓ hfeas hε0 hcomp hδ hδ')

end

/-! ## The bound on the query complexity -/

/-- Bounded-error quantum query complexity is at least
`(1 - (2√ε + ε))/2` times the adversary bound, for any error `ε` with
`2√ε + ε < 1`. -/
theorem mul_advPMOn_le_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ} [Nonempty O]
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1) :
    (1 - (2 * Real.sqrt ε + ε)) / 2 * advPMOn read f ≤ (qQueryOn read f ε : ℝ) := by
  classical
  refine le_qQueryOn_real (queryCounts_nonempty hdet hε0) fun q W' _ _ A hA => ?_
  have h := advPMOn_le_of_computes hε0 hlt hA
  linarith

/-- A concrete instance of the lower bound: at error `1/16` the constant is
`7/32`.  (The threshold `2√ε + ε < 1` holds for every `ε < 3 - 2√2 ≈ 0.1716`.) -/
theorem mul_advPMOn_le_qQueryOn_of_error_sixteenth {read : X → ι → σ} {f : X → O}
    [Nonempty O] (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) := by
  classical
  have hs : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h := mul_advPMOn_le_qQueryOn (read := read) (f := f) (ε := 1 / 16) hdet
    (by norm_num) (by rw [hs]; norm_num)
  rw [hs] at h
  norm_num at h
  linarith

end QuantumQueryComplexity

end SourceQuantumLowerBoundMain

section SourceQuantumLowerBoundOutputBool

/-!
# The sharp output condition, for Boolean outputs

`SourceQuantumLowerBoundOutput` bounds the final progress by `‖Γ‖(2√ε + ε)` for any decidable
output type; this section proves the **sharp** constant `2√(ε(1−ε))` when the
output is Boolean — which is what makes `ε = 1/3` work without amplification.

Two extra facts are available for `O = Bool`, and they are exactly what the
matrix-level argument needs:

* **The `B–B` term vanishes too.**  With two outcomes the error part is
  `B x = qRestrict p (!f x) (ψ x)`; on the support of `Γ` the outputs differ,
  so `!f x ≠ !f y` and the error parts are orthogonal — the same
  `qInner_qRestrict_of_ne` that killed the `A–A` term.  Only the two *cross*
  terms survive.
* **The masses are linked, not just bounded.**  `‖A‖² + ‖B‖² = 1` per input,
  so the weighted masses satisfy `∑‖δA‖² = 1 − β` with `β = ∑‖δB‖² ≤ ε`
  *exactly*, and the two cross terms are `√(1−β)√β' + √β√(1−β')`.

The scalar maximization `√(1−β)√β' + √β√(1−β') ≤ 2√(ε(1−ε))` for
`β, β' ∈ [0, ε]`, `ε ≤ 1/2` is where the sharp constant comes from: after the
AM–GM step `cc' ≤ 1 − (s² + s'²)/2` the square of the left side is at most
`(s+s')²(1−ss')`, whose maximum over `[0,√ε]²` is at the corner — proved by
two monotone steps, each an explicit product-of-nonnegatives factorization
(`poly_step`), no calculus.

No spectral decomposition, no Helstrom measurement theory: the same bridge as
`SourceQuantumLowerBoundOutput`, with the Boolean structure supplying the two extra facts.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The scalar maximization -/

private lemma poly_step {e s s' : ℝ} (hs0 : 0 ≤ s) (hs'0 : 0 ≤ s')
    (hse : s ≤ e) (hs'e : s' ≤ e) (he : e ^ 2 ≤ 1 / 2) :
    (s + s') ^ 2 * (1 - s * s') ≤ (e + s') ^ 2 * (1 - e * s') := by
  have he0 : 0 ≤ e := le_trans hs0 hse
  have hs'2 : s' ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hs'0 hs'e 2
  have hs2 : s ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hs0 hse 2
  have hes : e * s ≤ e ^ 2 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr hse)]
  have h1 : (0 : ℝ) ≤ 1 - 2 * s' ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2 := by linarith
  have hbracket : (0 : ℝ)
      ≤ (e + s) * (1 - 2 * s' ^ 2) + s' * (2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2) :=
    add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg hs'0 h2)
  have hfact : (e + s') ^ 2 * (1 - e * s') - (s + s') ^ 2 * (1 - s * s')
      = (e - s) * ((e + s) * (1 - 2 * s' ^ 2)
          + s' * (2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2)) := by ring
  have hnn := mul_nonneg (sub_nonneg.mpr hse) hbracket
  linarith [hfact, hnn]

private lemma poly_bound {e s s' : ℝ} (hs0 : 0 ≤ s) (hs'0 : 0 ≤ s')
    (hse : s ≤ e) (hs'e : s' ≤ e) (he : e ^ 2 ≤ 1 / 2) :
    (s + s') ^ 2 * (1 - s * s') ≤ 4 * e ^ 2 * (1 - e ^ 2) := by
  have he0 : 0 ≤ e := le_trans hs0 hse
  calc (s + s') ^ 2 * (1 - s * s')
      ≤ (e + s') ^ 2 * (1 - e * s') := poly_step hs0 hs'0 hse hs'e he
    _ = (s' + e) ^ 2 * (1 - s' * e) := by ring
    _ ≤ (e + e) ^ 2 * (1 - e * e) := poly_step hs'0 he0 hs'e le_rfl he
    _ = 4 * e ^ 2 * (1 - e ^ 2) := by ring

/-- **The linked cross-term maximization**: for masses `β, β' ∈ [0, ε]` with
`ε ≤ 1/2`, `√(1−β)√β' + √β√(1−β') ≤ 2√(ε(1−ε))`, with the maximum at the
corner `β = β' = ε`. -/
private lemma sqrt_cross_sum_le {β β' ε : ℝ} (hβ0 : 0 ≤ β) (hβ'0 : 0 ≤ β')
    (hβε : β ≤ ε) (hβ'ε : β' ≤ ε) (hε2 : ε ≤ 1 / 2) :
    Real.sqrt (1 - β) * Real.sqrt β' + Real.sqrt β * Real.sqrt (1 - β')
      ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hε0 : 0 ≤ ε := le_trans hβ0 hβε
  have hβ1 : β ≤ 1 := by linarith
  have hβ'1 : β' ≤ 1 := by linarith
  set s := Real.sqrt β with hs
  set s' := Real.sqrt β' with hs'
  set c := Real.sqrt (1 - β) with hc
  set c' := Real.sqrt (1 - β') with hc'
  set e := Real.sqrt ε with he
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = β := Real.sq_sqrt hβ0
  have hs'2 : s' ^ 2 = β' := Real.sq_sqrt hβ'0
  have hc2 : c ^ 2 = 1 - β := Real.sq_sqrt (by linarith)
  have hc'2 : c' ^ 2 = 1 - β' := Real.sq_sqrt (by linarith)
  have he2 : e ^ 2 = ε := Real.sq_sqrt hε0
  have hse : s ≤ e := by rw [hs, he]; exact Real.sqrt_le_sqrt hβε
  have hs'e : s' ≤ e := by rw [hs', he]; exact Real.sqrt_le_sqrt hβ'ε
  have heh : e ^ 2 ≤ 1 / 2 := by rw [he2]; exact hε2
  -- AM–GM on the cosine pair
  have hcc : c * c' ≤ 1 - (s ^ 2 + s' ^ 2) / 2 := by
    have hsq := sq_nonneg (c - c')
    rw [show (c - c') ^ 2 = c ^ 2 - 2 * (c * c') + c' ^ 2 from by ring,
      hc2, hc'2] at hsq
    rw [hs2, hs'2]
    linarith
  -- the squared left side, against the polynomial
  have hLsq : (c * s' + s * c') ^ 2 ≤ (s + s') ^ 2 * (1 - s * s') := by
    have h1 : (c * s' + s * c') ^ 2
        = (1 - β) * s' ^ 2 + s ^ 2 * (1 - β') + 2 * (s * s') * (c * c') := by
      rw [show (c * s' + s * c') ^ 2
          = c ^ 2 * s' ^ 2 + s ^ 2 * c' ^ 2 + 2 * (s * s') * (c * c') from by
        ring, hc2, hc'2]
    have h2 : 2 * (s * s') * (c * c')
        ≤ 2 * (s * s') * (1 - (s ^ 2 + s' ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hcc (by positivity)
    have h3 : (1 - β) * s' ^ 2 + s ^ 2 * (1 - β')
          + 2 * (s * s') * (1 - (s ^ 2 + s' ^ 2) / 2)
        = (s + s') ^ 2 * (1 - s * s') := by
      rw [← hs2, ← hs'2]; ring
    linarith [h1, h2, h3]
  have hpoly := poly_bound hs0 hs'0 hse hs'e heh
  -- conclude by monotone square root
  have hL0 : 0 ≤ c * s' + s * c' :=
    add_nonneg (mul_nonneg hc0 hs'0) (mul_nonneg hs0 hc'0)
  have hchain : (c * s' + s * c') ^ 2 ≤ (2 * Real.sqrt (ε * (1 - ε))) ^ 2 := by
    have hRsq : (2 * Real.sqrt (ε * (1 - ε))) ^ 2 = 4 * (ε * (1 - ε)) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ ε * (1 - ε))]
      norm_num
    rw [hRsq]
    calc (c * s' + s * c') ^ 2 ≤ (s + s') ^ 2 * (1 - s * s') := hLsq
      _ ≤ 4 * e ^ 2 * (1 - e ^ 2) := hpoly
      _ = 4 * (ε * (1 - ε)) := by rw [he2]; ring
  have hfin := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq hL0, Real.sqrt_sq (by positivity)] at hfin

/-! ## The sharp output condition -/

variable {X : Type} [Fintype X] [DecidableEq X]
variable {H : Type} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- **The sharp output condition for Boolean outputs.**  On final states that
are correct with probability at least `1 - ε`, `ε ≤ 1/2`, the progress of any
adversary matrix is at most `‖Γ‖ · 2√(ε(1−ε))`. -/
theorem abs_progress_output_le_bool {Γ : Matrix X X ℝ} {f : X → Bool}
    (hΓ : ∀ x y, f x = f y → Γ x y = 0)
    {ψ : X → (H → ℂ)} (hψ : ∀ x, IsQState (ψ x))
    {p : H → Bool} {ε : ℝ} (hε2 : ε ≤ 1 / 2)
    (hp : ∀ x, 1 - ε ≤ qProb p (ψ x) (f x))
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |progress Γ δ δ' ψ| ≤ ‖Γ‖ * (2 * Real.sqrt (ε * (1 - ε))) := by
  classical
  set A : X → (H → ℂ) := fun x => qRestrict p (f x) (ψ x) with hA
  set B : X → (H → ℂ) := fun x => ψ x - A x with hB
  have hsplit : ∀ x, ψ x = A x + B x := by
    intro x
    rw [hB]
    simp
  -- the Boolean structure: the error part announces the complement
  have hBres : ∀ x, B x = qRestrict p (!(f x)) (ψ x) := by
    intro x
    funext h
    simp only [hB, hA, Pi.sub_apply, qRestrict]
    cases hph : p h <;> cases hfx : f x <;> simp
  -- the norms
  have hnormA : ∀ x, qNormSq (A x) = qProb p (ψ x) (f x) := by
    intro x
    rw [hA, qProb_eq_qNormSq_qRestrict]
  have hnormB : ∀ x, qNormSq (B x) = 1 - qProb p (ψ x) (f x) := by
    intro x
    rw [hB, hA, qNormSq_sub_qRestrict, hψ x]
  -- the masses: bounded by `ε` and linked to the `A`-side exactly
  have hsumB : ∑ x, qNormSq (qScale δ B x) ≤ ε := by
    calc ∑ x, qNormSq (qScale δ B x)
        = ∑ x, δ x ^ 2 * (1 - qProb p (ψ x) (f x)) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormB x]
      _ ≤ ∑ x, δ x ^ 2 * ε :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp x]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ, one_mul]
  have hsumB' : ∑ y, qNormSq (qScale δ' B y) ≤ ε := by
    calc ∑ y, qNormSq (qScale δ' B y)
        = ∑ y, δ' y ^ 2 * (1 - qProb p (ψ y) (f y)) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormB y]
      _ ≤ ∑ y, δ' y ^ 2 * ε :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp y]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ', one_mul]
  have hB0 : 0 ≤ ∑ x, qNormSq (qScale δ B x) :=
    Finset.sum_nonneg fun x _ => qNormSq_nonneg _
  have hB'0 : 0 ≤ ∑ y, qNormSq (qScale δ' B y) :=
    Finset.sum_nonneg fun y _ => qNormSq_nonneg _
  have hAsum : ∑ x, qNormSq (qScale δ A x)
      = 1 - ∑ x, qNormSq (qScale δ B x) := by
    have h : ∀ x, qNormSq (qScale δ A x)
        = δ x ^ 2 - qNormSq (qScale δ B x) := by
      intro x
      rw [qNormSq_qScale, qNormSq_qScale, hnormA x, hnormB x]
      ring
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, hδ]
  have hA'sum : ∑ y, qNormSq (qScale δ' A y)
      = 1 - ∑ y, qNormSq (qScale δ' B y) := by
    have h : ∀ y, qNormSq (qScale δ' A y)
        = δ' y ^ 2 - qNormSq (qScale δ' B y) := by
      intro y
      rw [qNormSq_qScale, qNormSq_qScale, hnormA y, hnormB y]
      ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_sub_distrib, hδ']
  -- both diagonal terms vanish on the support of `Γ`
  have hAA : gramForm Γ (qScale δ A) (qScale δ' A) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have h0 : qInner (qScale δ A x) (qScale δ' A y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right, hA]
        rw [qInner_qRestrict_of_ne p hf]
        ring
      rw [h0]
      simp
  have hBB : gramForm Γ (qScale δ B) (qScale δ' B) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have hne : (!(f x)) ≠ (!(f y)) := by
        intro hcon
        apply hf
        have h2 := congrArg (fun b => !b) hcon
        simpa using h2
      have h0 : qInner (qScale δ B x) (qScale δ' B y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right,
          hBres x, hBres y, qInner_qRestrict_of_ne p hne]
        ring
      rw [h0]
      simp
  -- only the two cross terms survive
  have hexp : progress Γ δ δ' ψ
      = gramForm Γ (qScale δ A) (qScale δ' B)
        + gramForm Γ (qScale δ B) (qScale δ' A) := by
    have h1 : qScale δ ψ = fun x => qScale δ A x + qScale δ B x := by
      funext x
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ w x) (funext hsplit)
    have h2 : qScale δ' ψ = fun y => qScale δ' A y + qScale δ' B y := by
      funext y
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ' w y) (funext hsplit)
    rw [progress, h1, h2, gramForm_add_left, gramForm_add_right,
      gramForm_add_right, hAA, hBB]
    ring
  -- the two bridge bounds, with the linked masses
  have hb1 := abs_gramForm_le Γ (qScale δ A) (qScale δ' B)
  have hb2 := abs_gramForm_le Γ (qScale δ B) (qScale δ' A)
  rw [hAsum] at hb1
  rw [hA'sum] at hb2
  -- combine with the scalar maximization
  have hcross := sqrt_cross_sum_le hB0 hB'0 hsumB hsumB' hε2
  have hmul := mul_le_mul_of_nonneg_left hcross (norm_nonneg Γ)
  have habs := abs_add_le (gramForm Γ (qScale δ A) (qScale δ' B))
    (gramForm Γ (qScale δ B) (qScale δ' A))
  rw [hexp]
  linarith [hb1, hb2, hmul, habs]

end QuantumQueryComplexity

end SourceQuantumLowerBoundOutputBool

section SourceQuantumLowerBoundMainBool

/-!
# The adversary lower bound at the sharp Boolean constant

`SourceQuantumLowerBoundMain` proves the lower bound with output constant `2√ε + ε`, which
requires `ε < 3 − 2√2 ≈ 0.1716`.  For **Boolean** outputs the sharp constant
`2√(ε(1−ε))` of `SourceQuantumLowerBoundOutputBool` plugs into the same parametric endgame
(`advPMOn_le_of_bilinear`), and `2√(ε(1−ε)) < 1` holds for every
`ε < 1/2` — in particular at the conventional `ε = 1/3`:

    mul_advPMOn_le_qQueryOn_of_error_third :
      (1/36) · advPMOn read f ≤ Q_{1/3}(f)

promise-native, no amplification, no repetition compiler.  The constant check
behind `1/36` is `(3 − 2√2)/6 ≥ 1/36 ↔ 289 ≥ 288` — the sharp constant at
`ε = 1/3` is `(3 − 2√2)/6 ≈ 0.0286`, and `1/36 ≈ 0.0278` sits just under it.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]

section

variable {A : QAlg ι σ Bool W} {q : ℕ} {read : X → ι → σ} {f : X → Bool} {ε : ℝ}

/-- **The Boolean-sharp adversary bound**: a `q`-query algorithm with error
`ε ≤ 1/2` forces `(1 − 2√(ε(1−ε)))·advPMOn read f ≤ 2q`. -/
theorem advPMOn_le_of_computes_bool (hε2 : ε ≤ 1 / 2)
    (hlt : 2 * Real.sqrt (ε * (1 - ε)) < 1)
    (hcomp : ComputesWithErrorOn A q read f ε) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advPMOn read f ≤ 2 * q := by
  refine advPMOn_le_of_bilinear
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hlt ?_
  intro Γ hΓ hfeas δ δ' hδ hδ'
  have hout : |algProgress Γ δ δ' A read q|
      ≤ ‖Γ‖ * (2 * Real.sqrt (ε * (1 - ε))) := by
    rw [algProgress]
    exact abs_progress_output_le_bool (fun x y h => hΓ.2 x y h)
      (fun x => A.state_isQState (read x) q) hε2 (fun x => hcomp x) hδ hδ'
  exact abs_dotProduct_mulVec_le_of_algProgress hfeas hδ hδ' hout

end

/-- **The sharp lower bound on Boolean query complexity**: every `ε ≤ 1/2`
with `2√(ε(1−ε)) < 1` works — the threshold is `ε < 1/2`, not
`ε < 3 − 2√2`. -/
theorem mul_advPMOn_le_qQueryOn_bool {read : X → ι → σ} {f : X → Bool} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hlt : 2 * Real.sqrt (ε * (1 - ε)) < 1) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) / 2 * advPMOn read f
      ≤ (qQueryOn read f ε : ℝ) := by
  refine le_qQueryOn_real (queryCounts_nonempty hdet hε0) fun q W' _ _ A hA => ?_
  have h := advPMOn_le_of_computes_bool hε2 hlt hA
  linarith

/-- **The conventional-error instance**: `(1/36)·advPMOn read f ≤ Q_{1/3}(f)`
for Boolean `f`, promise-native. -/
theorem mul_advPMOn_le_qQueryOn_of_error_third {read : X → ι → σ}
    {f : X → Bool} (hdet : ∀ x y, read x = read y → f x = f y) :
    (1 / 36 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) := by
  have hs : Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3)) ≤ 17 / 36 := by
    calc Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))
        ≤ Real.sqrt ((17 / 36 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 17 / 36 := Real.sqrt_sq (by norm_num)
  have h := mul_advPMOn_le_qQueryOn_bool (read := read) (f := f) (ε := 1 / 3)
    hdet (by norm_num) (by norm_num) (by linarith [hs])
  have hcoef : (1 / 36 : ℝ)
      ≤ (1 - 2 * Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))) / 2 := by
    linarith [hs]
  rcases le_or_gt 0 (advPMOn read f) with hadv | hadv
  · calc (1 / 36 : ℝ) * advPMOn read f
        ≤ (1 - 2 * Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))) / 2 * advPMOn read f :=
          mul_le_mul_of_nonneg_right hcoef hadv
      _ ≤ (qQueryOn read f (1 / 3) : ℝ) := h
  · have hq : (0 : ℝ) ≤ (qQueryOn read f (1 / 3) : ℝ) := Nat.cast_nonneg _
    nlinarith

end QuantumQueryComplexity

end SourceQuantumLowerBoundMainBool

section SourceQuantumPlurality

/-!
# Plurality amplification, and the general-output `1/3` lower bound

For a **Boolean** output the sharp `1/3` lower bound
`(1/36)·ADV±ₚ(f) ≤ Q_{1/3}(f)` needs no amplification
(`SourceQuantumLowerBoundMainBool`); for a general finite output type the lower
bound was known only at the characterization's own error,
`(7/32)·ADV±ₚ(f) ≤ Q_{1/16}(f)`.  This section closes the gap by **plurality
amplification**: run a `1/3`-error algorithm `43` times independently and
announce the most frequent answer.

The analysis is an exponential-moment (Markov) bound, not a Chernoff bound
and not a binomial-tail library.  If `W` is the number of wrong runs, the
product structure of the independent-run compiler (`SourceQuantumProductRun`,
exact product statistics) gives

    E[2^W] = ∏ᵢ (1 + Pr[run i wrong]) ≤ (4/3)^43,

so `Pr[W ≥ 22] ≤ (4/3)^43 / 2^22 = 2^64 / 3^43 < 1/16`; and with at most
`21` wrong runs the correct answer has a strict majority, hence is the
plurality.  Thus

    Q_{1/16}(f) ≤ 43·Q_{1/3}(f)      (finite outputs),

and with the `1/16` lower bound, `(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)`.

Contents: the `k`-fold product realization over an arbitrary finite output
type (`Realizes.foldRec`, the Boolean `Realizes.fold` generalized); the
exponential-moment tail `sum_prod_tail_le`; the plurality readout
`plurality` and its majority lemma; `amplify_plurality` at general `k` and
`ε`; and the `43`-run endpoints.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]
variable {O : Type} [Fintype O] [DecidableEq O]

/-! The exponential-moment tail `sum_prod_tail_le` (with `wrongCount`) lives in
  `SourceQuantumTail`. -/

/-! ## The plurality readout -/

/-- How often `o` occurs in the record `y`. -/
def voteCount {k : ℕ} (y : Fin k → O) (o : O) : ℕ :=
  (Finset.univ.filter (fun j => y j = o)).card

/-- **The plurality readout**: the most frequent value of the record (the
earliest among ties). -/
def plurality {k : ℕ} (y : Fin (k + 1) → O) : O :=
  (((List.finRange (k + 1)).map y).argmax (voteCount y)).getD (y 0)

omit [Fintype O] in
/-- A strict majority is the plurality. -/
lemma plurality_eq_of_majority {k : ℕ} {y : Fin (k + 1) → O} {o : O}
    (h : k + 1 < 2 * voteCount y o) : plurality y = o := by
  set l := (List.finRange (k + 1)).map y with hl
  have hne : l ≠ [] :=
    List.ne_nil_of_mem (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  obtain ⟨m, hm⟩ : ∃ m, l.argmax (voteCount y) = some m := by
    rcases hmx : l.argmax (voteCount y) with _ | m
    · exact absurd (List.argmax_eq_none.mp hmx) hne
    · exact ⟨m, rfl⟩
  have hm' : m ∈ l.argmax (voteCount y) := by
    rw [hm]
    rfl
  have ho : o ∈ l := by
    have hpos : 0 < voteCount y o := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, (Finset.mem_filter.mp hj).2⟩
  have hle : voteCount y o ≤ voteCount y m := List.le_of_mem_argmax ho hm'
  have hmo : m = o := by
    by_contra hmo
    have hinter : (Finset.univ.filter (fun j => y j = m))
        ∩ (Finset.univ.filter (fun j => y j = o)) = ∅ := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact absurd (h1.symm.trans h2) hmo
      · intro hj
        simp at hj
    have hcard := Finset.card_union_add_card_inter
      (Finset.univ.filter (fun j => y j = m)) (Finset.univ.filter (fun j => y j = o))
    rw [hinter, Finset.card_empty, add_zero] at hcard
    have hle' : ((Finset.univ.filter (fun j => y j = m))
        ∪ (Finset.univ.filter (fun j => y j = o))).card ≤ k + 1 := by
      refine le_trans (Finset.card_le_univ _) ?_
      rw [Fintype.card_fin]
    have hsum : voteCount y m + voteCount y o ≤ k + 1 := by
      rw [voteCount, voteCount, ← hcard]
      exact hle'
    omega
  rw [plurality, hm, Option.getD_some, hmo]

omit [Fintype O] in
/-- A wrong plurality has at least `⌈(k+1)/2⌉` wrong runs. -/
lemma le_wrongCount_of_plurality_ne {k : ℕ} {y : Fin (k + 1) → O} {o : O}
    (h : plurality y ≠ o) :
    (k + 2) / 2 ≤ wrongCount y (fun _ => o) := by
  classical
  have hmaj : ¬ (k + 1 < 2 * voteCount y o) :=
    fun hc => h (plurality_eq_of_majority hc)
  have hsplit : voteCount y o + wrongCount y (fun _ => o) = k + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (k + 1) => y j = o)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  omega

/-! ## Plurality amplification -/

omit [Fintype O] [Fintype X] in
/-- **Plurality amplification.**  `k + 1` independent runs of an algorithm
with error `ε` for a finite-output function, read out by plurality, compute
the same function with error `(1 + ε)^{k+1} / 2^{⌈(k+1)/2⌉}`, at `k + 1`
times the cost. -/
theorem amplify_plurality {read : X → ι → σ} {f : X → O} {q : ℕ} {ε : ℝ}
    (hex : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ O W), ComputesWithErrorOn A q read f ε) (k : ℕ) [Finite O] :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O W'),
      ComputesWithErrorOn A' ((k + 1) * q) read f
        ((1 + ε) ^ (k + 1) / 2 ^ ((k + 2) / 2)) := by
  classical
  let := Fintype.ofFinite O
  obtain ⟨W, hW, hW', A, hA⟩ := hex
  have hbase : Realizes read q (fun x o => A.prob (read x) q o) :=
    ⟨W, hW, hW', A, fun _ _ => rfl⟩
  have hfold := Realizes.foldRec (k + 1) (fun _ => q)
    (fun _ x o => A.prob (read x) q o) (fun _ => hbase)
  have hcost : (∑ _j : Fin (k + 1), q) = (k + 1) * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  have hplur := hfold.map (plurality (k := k))
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hplur
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (f x)]
  -- the total mass is one
  have htotal : (∑ y : Fin (k + 1) → O, ∏ _j : Fin (k + 1),
      A.prob (read x) q (y _j)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin (k + 1)) o => A.prob (read x) q o)]
    simp [A.sum_prob]
  have hsplitsum := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y : Fin (k + 1) → O => plurality y = f x)
    (fun y => ∏ j, A.prob (read x) q (y j))
  rw [htotal] at hsplitsum
  -- the wrong values carry probability at most `ε`
  have hwrongprob : (∑ o ∈ Finset.univ.filter (fun o => o ≠ f x),
      A.prob (read x) q o) ≤ ε := by
    have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun o : O => o = f x) (fun o => A.prob (read x) q o)
    rw [A.sum_prob, Finset.filter_eq', ite_eq_left (Finset.mem_univ _),
      Finset.sum_singleton] at hsum
    have := hA x
    have hfilter : (Finset.univ.filter (fun o : O => ¬ o = f x))
        = Finset.univ.filter (fun o => o ≠ f x) := rfl
    rw [hfilter] at hsum
    linarith
  -- the wrong-plurality mass is small
  have hwrongmass : (∑ y ∈ Finset.univ.filter
        (fun y : Fin (k + 1) → O => ¬(plurality y = f x)),
      ∏ j, A.prob (read x) q (y j))
      ≤ (1 + ε) ^ (k + 1) / 2 ^ ((k + 2) / 2) := by
    have hsub : Finset.univ.filter
        (fun y : Fin (k + 1) → O => ¬(plurality y = f x))
        ⊆ Finset.univ.filter (fun y : Fin (k + 1) → O =>
          (k + 2) / 2 ≤ wrongCount y (fun _ => f x)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact le_wrongCount_of_plurality_ne hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun y _ _ => Finset.prod_nonneg fun j _ => A.prob_nonneg _ _ _) ?_
    rw [le_div_iff₀ (by positivity)]
    exact sum_prod_tail_le (fun _ o => A.prob (read x) q o) (fun _ => f x)
      (fun _ o => A.prob_nonneg _ _ _) (fun _ => le_of_eq (A.sum_prob _ _))
      (fun _ => hwrongprob)
  linarith [hsplitsum, hwrongmass]

/-! ## The `43`-run endpoints -/

omit [Fintype O] [Fintype X] in
/-- **`43` runs at error `1/3` give error below `1/16`**:
`(4/3)^43 / 2^22 = 2^64 / 3^43 < 1/16`. -/
theorem fortythree_mem_queryCounts_sixteenth {read : X → ι → σ} {f : X → O}
    {q : ℕ} (hq : q ∈ QueryCounts read f (1 / 3)) [Finite O] :
    43 * q ∈ QueryCounts read f (1 / 16) := by
  classical
  let := Fintype.ofFinite O
  obtain ⟨W', hW1, hW2, A', hA'⟩ := amplify_plurality hq 42
  exact ⟨W', hW1, hW2, A', hA'.mono (by norm_num)⟩

variable [Nonempty O] [DecidableEq X]

omit [DecidableEq X] [Fintype O] [Fintype X] in
/-- **`Q_{1/16}(f) ≤ 43·Q_{1/3}(f)`** for finite outputs. -/
theorem qQueryOn_sixteenth_le_fortythree_mul_third {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) [Finite O] [Finite X] :
    qQueryOn read f (1 / 16) ≤ 43 * qQueryOn read f (1 / 3) := by
  classical
  let := Fintype.ofFinite O
  let := Fintype.ofFinite X
  exact Nat.sInf_le (fortythree_mem_queryCounts_sixteenth
      (Nat.sInf_mem (queryCounts_nonempty hdet (by norm_num))))

omit [Fintype O] in
/-- **The general-output `1/3` lower bound**:
`(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)` for any finite nonempty output type, on
any promise.  `7/1376 = (7/32)/43`. -/
theorem mul_advPMOn_le_qQueryOn_third_finiteOutput {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) [Finite O] :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) := by
  classical
  let := Fintype.ofFinite O
  have h16 := mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet
  have h43 : ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ 43 * ((qQueryOn read f (1 / 3) : ℕ) : ℝ) := by
    exact_mod_cast qQueryOn_sixteenth_le_fortythree_mul_third hdet
  linarith

omit [Fintype O] in
/-- The total-function form: `(7/1376)·ADV±(f) ≤ Q_{1/3}(f)`. -/
theorem mul_advPM_le_qQuery_third_finiteOutput (f : (ι → σ) → O) [Finite O] :
    (7 / 1376 : ℝ) * advPM f ≤ (qQuery f (1 / 3) : ℝ) := by
  classical
  let := Fintype.ofFinite O
  have h := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (ι → σ) → ι → σ)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  exact h

end QuantumQueryComplexity

end SourceQuantumPlurality

section SourceQuantumCharacterization

/-!
# The fixed-error characterization for total Boolean functions

The first end-to-end deliverable of the quantum layer:

    (7/32) · ADV±(f)  ≤  Q_{1/16}(f)  ≤  2¹⁴ · ADV±(f)

for every total Boolean function `f : (ι → Bool) → Bool`
(`qQuery_characterized_by_advPM`).  The lower half is the operational bound
(`mul_advPMOn_le_qQueryOn_of_error_sixteenth` at `read = id`); the upper half
chains **strong duality** (`exists_dualPair_of_advPM_lt`, giving dual pairs
of cost arbitrarily close to `ADV±`), the total-to-promise restriction
(`HasDual.hasDualOn`), and uniform extraction
(`qQueryOn_le_of_hasDualOn_uniform`). Taking arbitrarily small slack gives
`Q_{1/16}(f) ≤ 8192(1 + ADV±(f))` without assuming an optimal dual exists.
For nonconstant functions, `one_le_advPM` supplies `ADV± ≥ 1`, so this is at
most `2¹⁴·ADV±`. Constant functions cost zero queries.

This module combines the strong-duality results in `Adversary` with the operational
quantum hierarchy. Build the complete project with `lake build LeanPool.QuantumQuery`.

The conventional-error form is here too
(`boundedErrorQQuery_characterized_by_advPM`):

    (1/36) · ADV±(f)  ≤  Q_{1/3}(f)  ≤  2¹⁴ · ADV±(f)

— the upper half by error monotonicity, the lower half by the **sharp Boolean
output condition** of `SourceQuantumLowerBoundOutputBool` (no amplification).

The oracle-simulation theorem (`SourceQuantumSimulation`) transports the
characterization into the conventional model
(`xorQQuery_characterized_by_advPM`, below): the **standard Boolean XOR
oracle with explicit idle-index and blank-answer sectors**, at two queries
per query.  Convention, stated for precision: that XOR model lives on the
same basis `Option ι × Option Bool × W`, acting as the textbook XOR on the
`some`-answer sector and as the identity on the idle and blank sectors; the
further padding equivalence to a literal `ι × Bool × W` basis is a standard
harmless extension and is not separately formalized.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The operational lower bound, for total Boolean functions**:
`(7/32)·ADV±(f) ≤ Q_{1/16}(f)`.  The total case uses `read = id`. -/
theorem mul_advPM_le_qQuery_sixteenth (f : (ι → Bool) → Bool) :
    (7 / 32 : ℝ) * advPM f ≤ (qQuery f (1 / 16) : ℝ) := by
  have h := mul_advPMOn_le_qQueryOn_of_error_sixteenth
    (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  replace h : (7 / 32 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 16) : ℝ) := h
  exact h

/-- **The additive uniform upper bound, for total Boolean functions**:
strong duality and uniform extraction give `Q_{1/16}(f) ≤ 8192(1 + ADV±(f))`.
Arbitrarily small slack suffices; dual optimizer attainment is not needed. -/
theorem qQuery_sixteenth_le_one_add_advPM (f : (ι → Bool) → Bool) :
    (qQuery f (1 / 16) : ℝ) ≤ 8192 * (1 + advPM f) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : advPM f < advPM f + ε / 8192 := by linarith
  obtain ⟨m, P, hP⟩ := exists_dualPair_of_advPM_lt hc
  have hd : HasDual f (advPM f + ε / 8192) := ⟨Fin m, inferInstance, P, hP⟩
  have hu := qQueryOn_le_of_hasDualOn_uniform hd.hasDualOn
    ((advPM_nonneg f).trans hc.le)
  change (qQuery f (1 / 16) : ℝ) ≤ 8192 * (1 + (advPM f + ε / 8192)) at hu
  linarith

/-- **The algorithmic upper bound, for total Boolean functions**:
`Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. The additive uniform bound absorbs its constant
term using `ADV± ≥ 1` for nonconstant functions; constants need no queries. -/
theorem qQuery_sixteenth_le_advPM (f : (ι → Bool) → Bool) :
    (qQuery f (1 / 16) : ℝ) ≤ 2 ^ 14 * advPM f := by
  by_cases hconst : ∀ x y : ι → Bool, f x = f y
  · have h0 : qQuery f (1 / 16) = 0 :=
      qQueryOn_const_eq_zero id (c := f (fun _ => false))
        (fun x => hconst x (fun _ => false)) (by norm_num)
    rw [h0, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (advPM_nonneg f)
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have h1 : 1 ≤ advPM f := one_le_advPM hxy
    linarith [qQuery_sixteenth_le_one_add_advPM f]

/-- **The fixed-error characterization for total Boolean functions**
: `(7/32)·ADV±(f) ≤ Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. -/
theorem qQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (7 / 32 : ℝ) * advPM f ≤ (qQuery f (1 / 16) : ℝ) ∧
      (qQuery f (1 / 16) : ℝ) ≤ 2 ^ 14 * advPM f :=
  ⟨mul_advPM_le_qQuery_sixteenth f, qQuery_sixteenth_le_advPM f⟩

/-- **The conventional-error upper bound is free** (error monotonicity):
`Q_{1/3}(f) ≤ Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. -/
theorem boundedErrorQQuery_le_advPM (f : (ι → Bool) → Bool) :
    (boundedErrorQQuery f : ℝ) ≤ 2 ^ 14 * advPM f := by
  have hne : (QueryCounts (id : (ι → Bool) → ι → Bool) f (1 / 16)).Nonempty :=
    queryCounts_nonempty (fun x y hxy => by rw [show x = y from hxy])
      (by norm_num)
  have hmono : qQuery f (1 / 3) ≤ qQuery f (1 / 16) :=
    qQueryOn_mono (by norm_num) hne
  have hmono' : (boundedErrorQQuery f : ℝ) ≤ (qQuery f (1 / 16) : ℝ) := by
    exact_mod_cast hmono
  linarith [hmono', qQuery_sixteenth_le_advPM f]

/-- **The conventional-error lower bound** for total Boolean functions:
`(1/36)·ADV±(f) ≤ Q_{1/3}(f)`, via the sharp Boolean output condition — no
amplification. -/
theorem mul_advPM_le_boundedErrorQQuery (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * advPM f ≤ (boundedErrorQQuery f : ℝ) := by
  have h := mul_advPMOn_le_qQueryOn_of_error_third
    (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  replace h : (1 / 36 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := h
  exact h

/-- **The conventional-error characterization** at `ε = 1/3`:
`(1/36)·ADV±(f) ≤ Q_{1/3}(f) ≤ 2¹⁴·ADV±(f)` for total Boolean `f`. -/
theorem boundedErrorQQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * advPM f ≤ (boundedErrorQQuery f : ℝ) ∧
      (boundedErrorQQuery f : ℝ) ≤ 2 ^ 14 * advPM f :=
  ⟨mul_advPM_le_boundedErrorQQuery f, boundedErrorQQuery_le_advPM f⟩

/-- **The characterization in the Boolean XOR-oracle model**: for total
Boolean `f`, at error `1/3`, using the idle and blank sectors of `SourceQuantumXorOracle`,

    (1/72)·ADV±(f) ≤ Qˣ_{1/3}(f) ≤ 2¹⁵·ADV±(f),

by the two-queries-per-query simulation of `SourceQuantumSimulation` applied
to the transposition-model characterization. -/
theorem xorQQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (1 / 72 : ℝ) * advPM f
        ≤ (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) ∧
      (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
        ≤ 2 ^ 15 * advPM f := by
  have hdet : ∀ x y : ι → Bool, (id x : ι → Bool) = id y → f x = f y :=
    fun x y hxy => by rw [show x = y from hxy]
  have h1 := qQueryOn_le_two_mul_xorQQueryOn hdet
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h2 := xorQQueryOn_le_two_mul_qQueryOn hdet
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h1' : (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 * (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := by
    exact_mod_cast h1
  have h2' : (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 * (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := by
    exact_mod_cast h2
  have hlow : (1 / 36 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) :=
    mul_advPM_le_boundedErrorQQuery f
  have hup : (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 ^ 14 * advPM f :=
    boundedErrorQQuery_le_advPM f
  constructor
  · linarith
  · linarith

/-! ## The promise-Boolean characterization

Promise strong duality (`SourceDualityMainOn`) feeds the promise-native
extraction, and the lower bound was promise-native from the start. -/

section Promise

variable {σ X : Type} [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]

/-- **The promise upper bound from the promise adversary bound.** -/
theorem qQueryOn_le_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
  by_cases hconst : ∀ x y : X, f x = f y
  · have h0 : qQueryOn read f (1 / 16) = 0 := by
      rcases isEmpty_or_nonempty X with he | hne
      · exact qQueryOn_const_eq_zero read (c := true)
          (fun x => (he.false x).elim) (by norm_num)
      · obtain ⟨x₀⟩ := hne
        exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hconst x x₀)
          (by norm_num)
    rw [h0, Nat.cast_zero]
    have hA0 := advPMOn_nonneg hdet
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
    nlinarith
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have hhalf := half_le_advPMOn hdet hxy
    obtain ⟨m, P, hP⟩ := exists_dualPairOn_of_advPMOn_lt hdet
      (show advPMOn read f < 2 * advPMOn read f from by linarith)
    have hup := qQueryOn_le_of_dualPairOn read f P hP (by linarith)
    have hb : 8192 * (1 + 4 * Real.sqrt (Fintype.card σ)
          * (2 * advPMOn read f))
        = 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
      ring
    linarith [hup, hb.le, hb.ge]

/-- **The promise-Boolean characterization at fixed error `1/16`**
: for any read-determined Boolean promise problem on a
finite **nonempty** alphabet,
`(7/32)·ADV±ₚ(f) ≤ Q_{1/16}(f) ≤ 8192(1 + 8√|σ|·ADV±ₚ(f))`.  The unsuffixed
name is the general-output theorem below. -/
theorem qQueryOn_characterized_by_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ)
    (f : X → Bool) (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) :=
  ⟨mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet,
    qQueryOn_le_advPMOn_bool_sixteenth read f hdet⟩

/-- The multiplicative form at `1/16`, for problems nonconstant on the
promise: `Q_{1/16}(f) ≤ 2¹⁷·√|σ|·ADV±ₚ(f)`. -/
theorem qQueryOn_le_mul_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ)
    (f : X → Bool) (hdet : ∀ x y, read x = read y → f x = f y)
    {x y : X} (hxy : f x ≠ f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 17 * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  have hup := qQueryOn_le_advPMOn_bool_sixteenth read f hdet
  have hhalf := half_le_advPMOn hdet hxy
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card σ) := by
    have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
    have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_le_sqrt h2
  have hprod : (1 : ℝ) * (1 / 2)
      ≤ Real.sqrt (Fintype.card σ) * advPMOn read f :=
    mul_le_mul hs1 hhalf (by norm_num) (Real.sqrt_nonneg _)
  linarith [hup, hprod]

/-- **The promise-Boolean characterization at bounded error `1/3`**: the
lower half is the sharp promise-native Boolean bound, the upper half is error
monotonicity into the `1/16` extraction. -/
theorem qQueryOn_characterized_by_advPMOn_bool_third [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (1 / 36 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
  constructor
  · exact mul_advPMOn_le_qQueryOn_of_error_third hdet
  · have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
      qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
    have hup := qQueryOn_le_advPMOn_bool_sixteenth read f hdet
    have hcast : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
        ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
    linarith

/-! ## Finite outputs (the bit-encoding route)

Each encoding bit of `f` is a post-composition, so its promise adversary
bound is at most `f`'s (`advPMOn_comp_le`); the promise-Boolean
characterization supplies a `1/16`-algorithm per bit, and the independent-run
machinery (`SourceQuantumAmplify`, `SourceQuantumFiniteOutput`) amplifies and joins them. -/

/-- **The general-output upper bound**: for `f : X → O` with `O` a finite
nonempty output type of `m` values, on any promise and finite nonempty
alphabet,

    Q_{1/16}(f) ≤ 2·B·(Nat.clog 2 (3B)) · 8192(1 + 8√|σ|·ADV±ₚ(f)),
    B = Nat.clog 2 m

(`Nat.clog 2 0 = 0`, so singleton outputs are included) — the
`O(log m · loglog m · √|σ| · ADV±ₚ)` shape, at the SAME fixed error
`1/16` as the lower bound: with `t = Nat.clog 2 (3B)` the assembled error is `0`
for `B = 0`, exactly `1/16` for `B = 1`, and at most `1/(9B) ≤ 1/18` for
`B ≥ 2`. -/
theorem qQueryOn_le_advPMOn_finiteOutput_sixteenth {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
            * advPMOn read f)) := by
  classical
  set B : ℕ := encBits O with hB
  set t : ℕ := Nat.clog 2 (3 * B) with ht
  -- the per-bit data
  have hdetb : ∀ i : Fin B, ∀ x y, read x = read y →
      encBit (f x) i = encBit (f y) i := fun i x y hxy => by
    rw [hdet x y hxy]
  have halg : ∀ i : Fin B, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A
        (qQueryOn read (fun x => encBit (f x) i) (1 / 16)) read
        (fun x => encBit (f x) i) (1 / 16) := fun i =>
    exists_computes_qQueryOn (queryCounts_nonempty (hdetb i) (by norm_num))
  -- the assembled algorithm
  obtain ⟨W', hW1, hW2, A', hA'⟩ := exists_decode_computes t halg
  -- its error is at most `1/16` (three cases: `B = 0`, `B = 1`, `B ≥ 2`)
  have herr : (B : ℝ) * (1 / 4) ^ t ≤ 1 / 16 := by
    have hpow : ∀ hB1 : 1 ≤ B, (3 * B : ℝ) ≤ 2 ^ t := by
      intro _
      have := Nat.le_pow_clog (by norm_num : 1 < 2) (3 * B)
      rw [← ht] at this
      exact_mod_cast this
    rcases Nat.lt_or_ge B 2 with hB2 | hB2
    · have hcase : B = 0 ∨ B = 1 := by omega
      rcases hcase with hB0 | hB1
      · rw [hB0]
        norm_num
      · -- `B = 1`: from `3 ≤ 2^t` the round count `t` is at least `2`
        have hpow1 : (3 : ℝ) ≤ 2 ^ t := by
          have := hpow (by omega)
          rw [hB1] at this
          norm_num at this
          exact_mod_cast this
        have ht2 : 2 ≤ t := by
          by_contra hcon
          have htle : t ≤ 1 := by omega
          have : (2 : ℝ) ^ t ≤ 2 ^ 1 :=
            pow_le_pow_right₀ (by norm_num) htle
          norm_num at this
          linarith
        have hq : ((1 : ℝ) / 4) ^ t ≤ (1 / 4) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) ht2
        rw [hB1]
        norm_num at hq ⊢
        linarith
    · -- `B ≥ 2`: the error is at most `1/(9B) ≤ 1/18`
      have hBpos' : (2 : ℝ) ≤ B := by exact_mod_cast hB2
      have hpow' := hpow (by omega)
      have h4 : ((1 : ℝ) / 4) ^ t = ((2 : ℝ) ^ t * (2 : ℝ) ^ t)⁻¹ := by
        rw [show ((1 : ℝ) / 4) = ((2 : ℝ) * 2)⁻¹ from by norm_num,
          inv_pow, mul_pow]
      have hkey : 16 * (B : ℝ) ≤ (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
        nlinarith [hpow', hBpos']
      rw [h4, mul_inv_le_iff₀ (by positivity)]
      linarith
  have hA3 : ComputesWithErrorOn A' (∑ i, 2 * t *
      qQueryOn read (fun x => encBit (f x) i) (1 / 16)) read f (1 / 16) :=
    hA'.mono herr
  -- the query count, bounded
  have hcount := qQueryOn_le hA3
  have hq0 : ∀ i : Fin B,
      ((qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℕ) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
    intro i
    have h1 := qQueryOn_le_advPMOn_bool_sixteenth read
      (fun x => encBit (f x) i) (hdetb i)
    have h2 : advPMOn read (fun x => encBit (f x) i) ≤ advPMOn read f :=
      advPMOn_comp_le hdet (fun o => encBit o i)
    have h3 : (0 : ℝ) ≤ 8 * Real.sqrt (Fintype.card σ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hcast : ((∑ i : Fin B, 2 * t *
      qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
    push_cast
    calc (∑ i : Fin B, (2 : ℝ) * t *
          (qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℝ))
        ≤ ∑ _i : Fin B, (2 : ℝ) * t
            * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hq0 i
          have ht0 : (0 : ℝ) ≤ 2 * t := by positivity
          nlinarith
      _ = (B : ℝ) * (2 * t)
            * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  have hfinal : ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
    refine le_trans ?_ hcast
    exact_mod_cast hcount
  calc ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) :=
        hfinal
    _ = 2 * (B : ℝ) * (t : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
        ring

/-- The conventional-error form, by monotonicity. -/
theorem qQueryOn_le_advPMOn_finiteOutput {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
            * advPMOn read f)) := by
  have h16 := qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet
  have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
    qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
  have hmono' : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
      ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-- **The finite-output characterization** (the reserved unsuffixed name):
the promise adversary bound characterizes fixed-error quantum query
complexity — the same error `1/16` on both sides — for any finite nonempty
output type, up to the alphabet factor `√|σ|` and a `log m · loglog m`
output factor. -/
theorem qQueryOn_characterized_by_advPMOn {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  ⟨mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet,
    qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet⟩

/-- **The finite-output characterization at the conventional error `1/3`**
 the lower half by plurality amplification over `43` runs
(`SourceQuantumPlurality`, `Q_{1/16} ≤ 43·Q_{1/3}`), the upper half by monotonicity
from the `1/16` bound.

    (7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)
      ≤ 2·B·(Nat.clog 2 (3B)) · 8192(1 + 8√|σ|·ADV±ₚ(f)),   B = Nat.clog 2 m. -/
theorem qQueryOn_characterized_by_advPMOn_third {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  ⟨mul_advPMOn_le_qQueryOn_third_finiteOutput hdet,
    qQueryOn_le_advPMOn_finiteOutput read f hdet⟩

/-- **The multiplicative asymptotic at the characterization's own error**:
absorbing the additive `1` via `half_le_advPMOn`,
`Q_{1/16}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f)`, `B = Nat.clog 2 m`
(`Nat.clog 2 0 = 0`). -/
theorem qQueryOn_le_mul_advPMOn_finiteOutput_sixteenth {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  by_cases hconst : ∀ x y : X, f x = f y
  · -- constant: zero queries; the right side is nonnegative
    have h0 : qQueryOn read f (1 / 16) = 0 := by
      rcases isEmpty_or_nonempty X with he | hne
      · exact qQueryOn_const_eq_zero read (c := Classical.arbitrary O)
          (fun x => (he.false x).elim) (by norm_num)
      · obtain ⟨x₀⟩ := hne
        exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hconst x x₀)
          (by norm_num)
    rw [h0, Nat.cast_zero]
    have hA0 := advPMOn_nonneg hdet
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
    have hB0 : (0 : ℝ) ≤ (encBits O : ℝ) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ (Nat.clog 2 (3 * encBits O) : ℝ) := Nat.cast_nonneg _
    positivity
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have hhalf := half_le_advPMOn hdet hxy
    have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card σ) := by
      have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
      have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_le_sqrt h2
    have hprod : (1 : ℝ) * (1 / 2)
        ≤ Real.sqrt (Fintype.card σ) * advPMOn read f :=
      mul_le_mul hs1 hhalf (by norm_num) (Real.sqrt_nonneg _)
    have h16 := qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet
    have hscalar : 8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
          * advPMOn read f)
        ≤ 2 ^ 17 * (Real.sqrt (Fintype.card σ) * advPMOn read f) := by
      nlinarith [hprod]
    have hBt0 : (0 : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hscalar hBt0
    calc (qQueryOn read f (1 / 16) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := h16
      _ ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (2 ^ 17 * (Real.sqrt (Fintype.card σ) * advPMOn read f)) := hmul
      _ = 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * Real.sqrt (Fintype.card σ) * advPMOn read f := by ring

/-- The conventional-error multiplicative form, by monotonicity. -/
theorem qQueryOn_le_mul_advPMOn_finiteOutput {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  have h16 := qQueryOn_le_mul_advPMOn_finiteOutput_sixteenth read f hdet
  have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
    qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
  have hmono' : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
      ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-- **The finite-output characterization at `1/3`, multiplicative**
 the plurality-amplified lower bound paired with the
multiplicative upper bound, so that "characterization" is literally a
two-sided proportionality —

    (7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f),
    B = Nat.clog 2 m. -/
theorem qQueryOn_characterized_by_advPMOn_third_mul {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  ⟨mul_advPMOn_le_qQueryOn_third_finiteOutput hdet,
    qQueryOn_le_mul_advPMOn_finiteOutput read f hdet⟩

end Promise

end QuantumQueryComplexity

end SourceQuantumCharacterization
