/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Ae Bridge -/

@[expose] public section

namespace Homogenization

/-!
# A.e.-ellipticity bridge (item C2)

The bridge that lets us replace an almost-everywhere-elliptic coefficient field
by an everywhere-elliptic one without changing the coarse block matrix.

* **C2(i)** — `Mu` and hence `coarseBlockMatrix` only see `a` up to a.e.
  equality on the (measurable) averaging set.
* **C2(ii)** — the elliptic locus `{x | IsEllipticMatrix 1 Θ (a x)}`, intersected
  with the averaging set, is measurable.  The proof avoids the matrix inverse:
  we replace the fourth ellipticity inequality `Θ⁻¹|ξ|² ≤ ξ·A⁻¹ξ` by the
  inverse-free image bound `|Aη|² ≤ Θ (η·Aη)` (equivalent, given coercivity),
  which makes the whole ellipticity locus a **closed** subset of the matrix-entry
  space — no countable dense reduction is needed.
* **C2(iii)** — the elliptic truncation `ellipticTruncate Θ a`, which agrees with
  `a` on the a.e.-elliptic set and is everywhere `(1, Θ)`-elliptic.
* **C2(iv)** — the consumer-facing packaging.

Vectors are `Vec d = Fin d → ℝ`; matrices `Mat d = Matrix (Fin d) (Fin d) ℝ`,
which is definitionally the entry space `Fin d → Fin d → ℝ`.  No `EuclideanSpace`.
-/

open MeasureTheory
open scoped Classical

variable {d : ℕ} {Θ : ℝ} {a a' : CoeffField d}

/-! ## C2(i) — `Mu` / `coarseBlockMatrix` a.e.-congruence -/

/-- The block energy density only depends on the coefficient field pointwise, so
it is insensitive to changing `a` on a null set. -/
theorem Mu_congr_of_ae_eq {U : Set (Vec d)}
    (hae : a =ᵐ[volume.restrict U] a') (P : BlockVec d) :
    Mu U P a = Mu U P a' := by
  have hset : muValueSet U P a = muValueSet U P a' := by
    have hvol : ∀ X : BlockState d,
        volumeAverage U (blockEnergyDensity a X) =
          volumeAverage U (blockEnergyDensity a' X) := by
      intro X
      unfold volumeAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp [blockEnergyDensity, blockCoeffField, hx]
    ext s
    constructor
    · rintro ⟨X, hX, rfl⟩; exact ⟨X, hX, hvol X⟩
    · rintro ⟨X, hX, rfl⟩; exact ⟨X, hX, (hvol X).symm⟩
  unfold Mu; rw [hset]

/-- Corollary of C2(i): the coarse block matrix is insensitive to a null-set
change of the coefficient field. -/
theorem coarseBlockMatrix_congr_of_ae_eq {U : Set (Vec d)}
    (hae : a =ᵐ[volume.restrict U] a') :
    coarseBlockMatrix U a = coarseBlockMatrix U a' :=
  coarseBlockMatrix_eq_of_mu_eq (fun P => Mu_congr_of_ae_eq hae P)

/-! ## C2(ii) — measurability of the elliptic locus

The inverse-free reformulation of the `(1, Θ)` ellipticity class. -/

/-- The two inverse-free ellipticity inequalities, as a predicate on the
matrix-entry space `Mat d = Fin d → Fin d → ℝ`. -/
def IsEllipticEntry (Θ : ℝ) (v : Mat d) : Prop :=
  (∀ ξ : Vec d, vecNormSq ξ ≤ vecDot ξ (matVecMul v ξ)) ∧
    (∀ η : Vec d, vecNormSq (matVecMul v η) ≤ Θ * vecDot η (matVecMul v η))

/-- **Inverse-free characterization.**  For the base constant `lam = 1`, the
`A⁻¹` inequality is equivalent to the image bound `|Aη|² ≤ Θ (η·Aη)`. -/
theorem isEllipticMatrix_one_iff (A : Mat d) :
    IsEllipticMatrix 1 Θ A ↔ 1 ≤ Θ ∧ IsEllipticEntry Θ A := by
  constructor
  · intro hA
    refine ⟨hA.2.1, fun ξ => ?_, fun η => ?_⟩
    · simpa using hA.2.2.1 ξ
    · have h := vecNormSq_matVecMul_le_mul_vecDot_symmPart_of_isEllipticMatrix hA η
      rwa [vecDot_matVecMul_symmPart] at h
  · rintro ⟨hΘ, hc, himg⟩
    have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘ
    -- coercivity forces `matVecMul A` to be injective, hence `A` invertible
    have hlin : ∀ x y : Vec d, matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
      intro x y; funext i
      simp [matVecMul, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]
    have hinj : Function.Injective (matVecMul A) := by
      intro x y hxy
      have hz : matVecMul A (x - y) = 0 := by rw [hlin, hxy]; simp
      have hcz := hc (x - y)
      rw [hz, vecDot_zero_right] at hcz
      have hzero : vecNormSq (x - y) = 0 := le_antisymm hcz (vecNormSq_nonneg _)
      exact sub_eq_zero.mp (vecNormSq_eq_zero hzero)
    have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    refine ⟨one_pos, hΘ, fun ξ => by simpa using hc ξ, fun ξ => ?_⟩
    -- reconstruct the `A⁻¹` inequality at `η = A⁻¹ ξ`
    set η := matVecMul A⁻¹ ξ with hη
    have hAη : matVecMul A η = ξ := by
      rw [hη, matVecMul_mul, Matrix.mul_nonsing_inv A hdet, matVecMul_one]
    have himgη := himg η
    rw [hAη] at himgη
    -- `himgη : vecNormSq ξ ≤ Θ * vecDot η ξ`
    have hdot : vecDot η ξ = vecDot ξ (matVecMul A⁻¹ ξ) := by rw [hη, vecDot_comm]
    rw [hdot] at himgη
    -- divide by `Θ`
    have hthis := mul_le_mul_of_nonneg_left himgη (le_of_lt (inv_pos.mpr hΘpos))
    rw [← mul_assoc, inv_mul_cancel₀ hΘpos.ne', one_mul] at hthis
    simpa using hthis

/-- The inverse-free ellipticity locus is closed in the matrix-entry space
`Fin d → Fin d → ℝ` (definitionally `Mat d`), which carries the product Borel
structure. -/
theorem isClosed_isEllipticEntry :
    IsClosed {v : Fin d → Fin d → ℝ | IsEllipticEntry Θ v} := by
  have h1 : IsClosed
      {v : Fin d → Fin d → ℝ | ∀ ξ : Vec d, vecNormSq ξ ≤ vecDot ξ (matVecMul v ξ)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter (fun ξ => ?_)
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed
      {v : Fin d → Fin d → ℝ |
        ∀ η : Vec d, vecNormSq (matVecMul v η) ≤ Θ * vecDot η (matVecMul v η)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter (fun η => ?_)
    simp only [vecNormSq, vecDot, matVecMul]
    exact isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter h2

/-- **C2(ii).**  Given the `IsEllipticFieldOn`-style entrywise measurability of the
`U`-truncated coefficient field, the elliptic locus intersected with `U` is
measurable. -/
theorem measurableSet_isEllipticMatrix_inter {U : Set (Vec d)}
    (hU : MeasurableSet U)
    (hmeasA : Measurable (fun x => fun i j => if x ∈ U then a x i j else 0)) :
    MeasurableSet (U ∩ {x | IsEllipticMatrix 1 Θ (a x)}) := by
  classical
  by_cases hΘ : 1 ≤ Θ
  · -- on `U`, the truncated field agrees with `a`, and membership reduces to a
    -- closed condition on the entries
    set ê : Vec d → (Fin d → Fin d → ℝ) :=
      fun x => fun i j => if x ∈ U then a x i j else 0 with hê
    have hpre : MeasurableSet (ê ⁻¹' {v : Fin d → Fin d → ℝ | IsEllipticEntry Θ v}) :=
      (isClosed_isEllipticEntry (Θ := Θ)).measurableSet.preimage hmeasA
    have hset :
        U ∩ {x | IsEllipticMatrix 1 Θ (a x)} =
          U ∩ (ê ⁻¹' {v : Fin d → Fin d → ℝ | IsEllipticEntry Θ v}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hxU, hell⟩
        refine ⟨hxU, ?_⟩
        have haê : ê x = a x := by funext i j; simp [hê, hxU]
        rw [haê]
        exact ((isEllipticMatrix_one_iff (a x)).mp hell).2
      · rintro ⟨hxU, hentry⟩
        refine ⟨hxU, ?_⟩
        have haê : ê x = a x := by funext i j; simp [hê, hxU]
        rw [haê] at hentry
        exact (isEllipticMatrix_one_iff (a x)).mpr ⟨hΘ, hentry⟩
    rw [hset]
    exact hU.inter hpre
  · -- when `Θ < 1` the locus is empty
    have hempty : U ∩ {x | IsEllipticMatrix 1 Θ (a x)} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro _ hell
      exact hΘ hell.2.1
    rw [hempty]
    exact MeasurableSet.empty

/-! ## C2(iii) — the elliptic truncation -/

/-- The elliptic truncation: keep `a x` where it is `(1, Θ)`-elliptic, otherwise
replace it by the identity (which is `(1, Θ)`-elliptic whenever `1 ≤ Θ`). -/
noncomputable def ellipticTruncate (Θ : ℝ) (a : CoeffField d) : CoeffField d :=
  fun x => by classical exact if IsEllipticMatrix 1 Θ (a x) then a x else 1

theorem ellipticTruncate_of_elliptic {x : Vec d} (h : IsEllipticMatrix 1 Θ (a x)) :
    ellipticTruncate Θ a x = a x := by
  classical simp [ellipticTruncate, h]

theorem ellipticTruncate_of_not_elliptic {x : Vec d} (h : ¬ IsEllipticMatrix 1 Θ (a x)) :
    ellipticTruncate Θ a x = 1 := by
  classical simp [ellipticTruncate, h]

/-- The identity matrix is `(1, Θ)`-elliptic whenever `1 ≤ Θ`. -/
theorem isEllipticMatrix_one_one (hΘ : 1 ≤ Θ) :
    IsEllipticMatrix 1 Θ (1 : Mat d) := by
  have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘ
  refine ⟨one_pos, hΘ, fun ξ => ?_, fun ξ => ?_⟩
  · simp [matVecMul_one, vecNormSq]
  · rw [inv_one, matVecMul_one]
    have hle : Θ⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hΘpos]; exact hΘ
    have : Θ⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ :=
      mul_le_mul_of_nonneg_right hle (vecNormSq_nonneg ξ)
    simpa [vecNormSq] using this

/-- Every truncated matrix is `(1, Θ)`-elliptic, given `1 ≤ Θ`. -/
theorem isEllipticMatrix_ellipticTruncate (hΘ : 1 ≤ Θ) (x : Vec d) :
    IsEllipticMatrix 1 Θ (ellipticTruncate Θ a x) := by
  classical
  by_cases h : IsEllipticMatrix 1 Θ (a x)
  · rw [ellipticTruncate_of_elliptic h]; exact h
  · rw [ellipticTruncate_of_not_elliptic h]; exact isEllipticMatrix_one_one hΘ

/-- **C2(iii)(a).**  The elliptic truncation is an everywhere-`(1, Θ)`-elliptic
field on `U`, given `1 ≤ Θ` and the entrywise measurability of the `U`-truncated
coefficient field. -/
theorem isEllipticFieldOn_ellipticTruncate {U : Set (Vec d)} (hU : MeasurableSet U)
    (hΘ : 1 ≤ Θ)
    (hmeasA : Measurable (fun x => fun i j => if x ∈ U then a x i j else 0)) :
    IsEllipticFieldOn 1 Θ U (ellipticTruncate Θ a) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_ellipticTruncate hΘ x⟩
  -- measurability of the truncated truncation field
  have hUE : MeasurableSet (U ∩ {x | IsEllipticMatrix 1 Θ (a x)}) :=
    measurableSet_isEllipticMatrix_inter hU hmeasA
  refine measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => ?_))
  have hê : Measurable (fun x => (if x ∈ U then a x i j else 0)) := by
    have := (measurable_pi_iff.mp (measurable_pi_iff.mp hmeasA i)) j
    simpa using this
  -- rewrite the field entrywise as a nested piecewise
  have hfun :
      (fun x => if x ∈ U then (ellipticTruncate Θ a x) i j else 0) =
        (U ∩ {x | IsEllipticMatrix 1 Θ (a x)}).piecewise
          (fun x => if x ∈ U then a x i j else 0)
          (U.piecewise (fun _ => (1 : Mat d) i j) (fun _ => 0)) := by
    funext x
    by_cases hxU : x ∈ U
    · by_cases hell : IsEllipticMatrix 1 Θ (a x)
      · simp [Set.piecewise, hxU, hell, ellipticTruncate_of_elliptic hell]
      · simp [Set.piecewise, hxU, hell, ellipticTruncate_of_not_elliptic hell]
    · simp [Set.piecewise, hxU]
  rw [hfun]
  exact Measurable.piecewise hUE hê (Measurable.piecewise hU measurable_const measurable_const)

/-- **C2(iii)(b).**  On the a.e.-elliptic set, the truncation equals `a`. -/
theorem ellipticTruncate_ae_eq {U : Set (Vec d)}
    (hae : ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix 1 Θ (a x)) :
    ellipticTruncate Θ a =ᵐ[volume.restrict U] a := by
  filter_upwards [hae] with x hx
  exact ellipticTruncate_of_elliptic hx

/-! ## C2(iv) — bridge packaging -/

/-- **C2(iv).**  From a.e. ellipticity on the (measurable) averaging set plus the
entrywise measurability of the `U`-truncated field (and `1 ≤ Θ`), produce a
genuinely `(1, Θ)`-elliptic field `a'` that agrees with `a` a.e. on `U`, gives
the same coarse block matrix, and the same block coefficient field a.e. -/
theorem exists_ellipticFieldOn_ae_eq {U : Set (Vec d)} (hU : MeasurableSet U)
    (hΘ : 1 ≤ Θ)
    (hmeasA : Measurable (fun x => fun i j => if x ∈ U then a x i j else 0))
    (hae : ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix 1 Θ (a x)) :
    ∃ a' : CoeffField d,
      IsEllipticFieldOn 1 Θ U a' ∧
        a' =ᵐ[volume.restrict U] a ∧
        coarseBlockMatrix U a' = coarseBlockMatrix U a ∧
        (∀ᵐ x ∂(volume.restrict U), blockCoeffField a' x = blockCoeffField a x) := by
  refine ⟨ellipticTruncate Θ a, isEllipticFieldOn_ellipticTruncate hU hΘ hmeasA,
    ellipticTruncate_ae_eq hae, ?_, ?_⟩
  · exact coarseBlockMatrix_congr_of_ae_eq (ellipticTruncate_ae_eq hae)
  · filter_upwards [ellipticTruncate_ae_eq (Θ := Θ) (a := a) hae] with x hx
    simp [blockCoeffField, hx]

end Homogenization
