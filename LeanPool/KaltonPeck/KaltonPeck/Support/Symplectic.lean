/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Coordinates
public import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The canonical symplectic structure

This file constructs the canonical Kalton--Swanson symplectic form, transports it to arbitrary
Kalton--Peck presentations, and develops the associated block-operator theory.
-/

@[expose] public section


namespace KaltonPeck.Support.Symplectic

noncomputable
section

open Coordinates
open scoped lp

/-- Classical decidability used by the private block-coordinate definitions. -/
local instance classicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem memlpTwoIff (x : ℕ → ℝ) : Memℓp x 2 ↔ IsSquareSummable x := by
  simpa [IsSquareSummable, Real.norm_eq_abs, sq_abs] using
    (memℓp_gen_iff (p := (2 : ENNReal)) (f := x) (by norm_num))

/-- View a square-summable real sequence as a Hilbert-space vector. -/
def toL2 (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    lp (fun _ : ℕ ↦ ℝ) 2 :=
  ⟨(x : PreLp (fun _ : ℕ ↦ ℝ)), (by exact (memlpTwoIff x).2 hx)⟩

private theorem l2Norm_toL2 (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    l2Norm x = ‖toL2 x hx‖ := by
  rw [lp.norm_eq_tsum_rpow (p := (2 : ENNReal)) (by norm_num)]
  change Real.sqrt (∑' n, x n ^ 2) =
    (∑' n, |x n| ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro n
  calc
    x n ^ (2 : ℕ) = |x n| ^ (2 : ℕ) := (sq_abs (x n)).symm
    _ = |x n| ^ (2 : ℝ) := (Real.rpow_natCast |x n| 2).symm

/-- The real Hilbert space of square-summable sequences. -/
abbrev L2 := lp (fun _ : ℕ ↦ ℝ) 2

/-- Summability and bounds for the coordinate pairing used to construct the symplectic duality. -/
structure StrongPairingData : Prop where
  sectionSummable : ∀ (p : (ℕ → ℝ) × (ℕ → ℝ)) (y : ℕ → ℝ),
    IsAdmissiblePair p → IsSquareSummable y →
      Summable (fun n ↦ p.1 n * y n - p.2 n * centralizer y n)
  sectionBound : ∀ (p : (ℕ → ℝ) × (ℕ → ℝ)) (y : ℕ → ℝ),
    IsAdmissiblePair p → IsSquareSummable y →
      |∑' n, (p.1 n * y n - p.2 n * centralizer y n)| ≤
        (l2Norm (p.1 - centralizer p.2) + 4 * l2Norm p.2) * l2Norm y

private theorem strongPairingData : StrongPairingData where
  sectionSummable := canonicalPairingData.1
  sectionBound := canonicalPairingData.2

/-- The alternating coordinate summand for two Kalton–Peck coordinate pairs. -/
def canonicalPairingTerm
    (p q : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) : ℝ :=
  p.1 n * q.2 n - q.1 n * p.2 n

/-- The sum of the alternating coordinate pairing. -/
def canonicalPairing
    (p q : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  ∑' n, canonicalPairingTerm p q n

private theorem canonicalPairing_summable (D : StrongPairingData)
    (p q : (ℕ → ℝ) × (ℕ → ℝ))
    (hp : IsAdmissiblePair p) (hq : IsAdmissiblePair q) :
    Summable (canonicalPairingTerm p q) := by
  have hs := D.sectionSummable p q.2 hp hq.1
  have hi : Summable (fun n ↦ (q.1 - centralizer q.2) n * p.2 n) := by
    change Summable (fun n ↦ inner ℝ
      (toL2 p.2 hp.1 n) (toL2 (q.1 - centralizer q.2) hq.2 n))
    exact lp.summable_inner _ _
  exact (hs.sub hi).congr (fun n ↦ by
    simp [canonicalPairingTerm]
    ring)

private theorem canonicalPairing_decomp (D : StrongPairingData)
    (p q : (ℕ → ℝ) × (ℕ → ℝ))
    (hp : IsAdmissiblePair p) (hq : IsAdmissiblePair q) :
    canonicalPairing p q =
      (∑' n, (p.1 n * q.2 n - p.2 n * centralizer q.2 n)) -
        ∑' n, (q.1 - centralizer q.2) n * p.2 n := by
  rw [canonicalPairing, ← Summable.tsum_sub]
  · apply tsum_congr
    intro n
    simp [canonicalPairingTerm]
    ring
  · exact D.sectionSummable p q.2 hp hq.1
  · change Summable (fun n ↦ inner ℝ
      (toL2 p.2 hp.1 n) (toL2 (q.1 - centralizer q.2) hq.2 n))
    exact lp.summable_inner _ _

private theorem canonicalPairing_bound (D : StrongPairingData)
    (p q : (ℕ → ℝ) × (ℕ → ℝ))
    (hp : IsAdmissiblePair p) (hq : IsAdmissiblePair q) :
    |canonicalPairing p q| ≤ 5 * kaltonPeckQuasiNorm p * kaltonPeckQuasiNorm q := by
  let a := l2Norm (p.1 - centralizer p.2)
  let x := l2Norm p.2
  let b := l2Norm (q.1 - centralizer q.2)
  let y := l2Norm q.2
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hs := D.sectionBound p q.2 hp hq.1
  have hi : |∑' n, (q.1 - centralizer q.2) n * p.2 n| ≤ x * b := by
    have h := abs_real_inner_le_norm
      (toL2 p.2 hp.1) (toL2 (q.1 - centralizer q.2) hq.2)
    rw [lp.inner_eq_tsum] at h
    rw [← l2Norm_toL2 p.2 hp.1,
      ← l2Norm_toL2 (q.1 - centralizer q.2) hq.2] at h
    simpa only [toL2, RCLike.inner_apply, conj_trivial, mul_comm] using h
  rw [canonicalPairing_decomp D p q hp hq]
  calc
    |_ - _| ≤ |∑' n, (p.1 n * q.2 n - p.2 n * centralizer q.2 n)| +
        |∑' n, (q.1 - centralizer q.2) n * p.2 n| := abs_sub _ _
    _ ≤ (a + 4 * x) * y + x * b := add_le_add hs hi
    _ ≤ 5 * (a + x) * (b + y) := by
      nlinarith [mul_nonneg ha hb, mul_nonneg ha hy, mul_nonneg hx hb, mul_nonneg hx hy]
    _ = 5 * kaltonPeckQuasiNorm p * kaltonPeckQuasiNorm q := by
      rfl

/-- The alternating coordinate pairing as a bilinear map on the canonical model. -/
def pairingLinearMap (D : StrongPairingData) :
    CanonicalRealKaltonPeck →ₗ[ℝ] CanonicalRealKaltonPeck →ₗ[ℝ] ℝ :=
  { toFun := fun z ↦
      { toFun := fun w ↦ canonicalPairing
          (canonicalRealKaltonPeckPresentation.coordinates z)
          (canonicalRealKaltonPeckPresentation.coordinates w)
        map_add' := by
          intro w w'
          have hs := canonicalPairing_summable D
            (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w)
            (canonicalRealKaltonPeckPresentation.coordinates_mem z)
            (canonicalRealKaltonPeckPresentation.coordinates_mem w)
          have hs' := canonicalPairing_summable D
            (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w')
            (canonicalRealKaltonPeckPresentation.coordinates_mem z)
            (canonicalRealKaltonPeckPresentation.coordinates_mem w')
          rw [map_add]
          have hterm : canonicalPairingTerm
              (canonicalRealKaltonPeckPresentation.coordinates z)
              (canonicalRealKaltonPeckPresentation.coordinates w +
                canonicalRealKaltonPeckPresentation.coordinates w') =
              fun n ↦ canonicalPairingTerm
                (canonicalRealKaltonPeckPresentation.coordinates z)
                (canonicalRealKaltonPeckPresentation.coordinates w) n +
              canonicalPairingTerm
                (canonicalRealKaltonPeckPresentation.coordinates z)
                (canonicalRealKaltonPeckPresentation.coordinates w') n := by
            funext n
            simp [canonicalPairingTerm]
            ring
          simp only [canonicalPairing]
          rw [hterm, hs.tsum_add hs']
        map_smul' := by
          intro c w
          have hs := canonicalPairing_summable D
            (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w)
            (canonicalRealKaltonPeckPresentation.coordinates_mem z)
            (canonicalRealKaltonPeckPresentation.coordinates_mem w)
          rw [map_smul]
          have hterm : canonicalPairingTerm
              (canonicalRealKaltonPeckPresentation.coordinates z)
              (c • canonicalRealKaltonPeckPresentation.coordinates w) =
              fun n ↦ c * canonicalPairingTerm
                (canonicalRealKaltonPeckPresentation.coordinates z)
                (canonicalRealKaltonPeckPresentation.coordinates w) n := by
            funext n
            simp [canonicalPairingTerm]
            ring
          simp only [canonicalPairing]
          rw [hterm]
          simpa only [smul_eq_mul, RingHom.id_apply] using tsum_mul_left
          }
    map_add' := by
      intro z z'
      ext w
      change canonicalPairing
          (canonicalRealKaltonPeckPresentation.coordinates (z + z'))
          (canonicalRealKaltonPeckPresentation.coordinates w) =
        canonicalPairing (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w) +
          canonicalPairing (canonicalRealKaltonPeckPresentation.coordinates z')
            (canonicalRealKaltonPeckPresentation.coordinates w)
      have hs := canonicalPairing_summable D
        (canonicalRealKaltonPeckPresentation.coordinates z)
        (canonicalRealKaltonPeckPresentation.coordinates w)
        (canonicalRealKaltonPeckPresentation.coordinates_mem z)
        (canonicalRealKaltonPeckPresentation.coordinates_mem w)
      have hs' := canonicalPairing_summable D
        (canonicalRealKaltonPeckPresentation.coordinates z')
        (canonicalRealKaltonPeckPresentation.coordinates w)
        (canonicalRealKaltonPeckPresentation.coordinates_mem z')
        (canonicalRealKaltonPeckPresentation.coordinates_mem w)
      rw [map_add]
      have hterm : canonicalPairingTerm
          (canonicalRealKaltonPeckPresentation.coordinates z +
            canonicalRealKaltonPeckPresentation.coordinates z')
          (canonicalRealKaltonPeckPresentation.coordinates w) =
          fun n ↦ canonicalPairingTerm
            (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w) n +
          canonicalPairingTerm
            (canonicalRealKaltonPeckPresentation.coordinates z')
            (canonicalRealKaltonPeckPresentation.coordinates w) n := by
        funext n
        simp [canonicalPairingTerm]
        ring
      simp only [canonicalPairing]
      rw [hterm, hs.tsum_add hs']
    map_smul' := by
      intro c z
      ext w
      change canonicalPairing
          (canonicalRealKaltonPeckPresentation.coordinates (c • z))
          (canonicalRealKaltonPeckPresentation.coordinates w) =
        c * canonicalPairing (canonicalRealKaltonPeckPresentation.coordinates z)
          (canonicalRealKaltonPeckPresentation.coordinates w)
      have hs := canonicalPairing_summable D
        (canonicalRealKaltonPeckPresentation.coordinates z)
        (canonicalRealKaltonPeckPresentation.coordinates w)
        (canonicalRealKaltonPeckPresentation.coordinates_mem z)
        (canonicalRealKaltonPeckPresentation.coordinates_mem w)
      rw [map_smul]
      have hterm : canonicalPairingTerm
          (c • canonicalRealKaltonPeckPresentation.coordinates z)
          (canonicalRealKaltonPeckPresentation.coordinates w) =
          fun n ↦ c * canonicalPairingTerm
            (canonicalRealKaltonPeckPresentation.coordinates z)
            (canonicalRealKaltonPeckPresentation.coordinates w) n := by
        funext n
        simp [canonicalPairingTerm]
        ring
      simp only [canonicalPairing]
      rw [hterm]
      simpa only [smul_eq_mul, RingHom.id_apply] using tsum_mul_left
      }

/-- The bounded map to the strong dual supplied by the coordinate pairing. -/
def pairingContinuousLinearMap (D : StrongPairingData) :
    CanonicalRealKaltonPeck →L[ℝ] StrongDual ℝ CanonicalRealKaltonPeck := by
  let c : ℝ := Classical.choose canonicalRealKaltonPeckPresentation.norm_equivalent
  let C : ℝ := Classical.choose
    (Classical.choose_spec canonicalRealKaltonPeckPresentation.norm_equivalent)
  have hdata : 0 < c ∧ 0 < C ∧ ∀ z,
      c * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤ ‖z‖ ∧
        ‖z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates z) :=
    Classical.choose_spec (Classical.choose_spec
      canonicalRealKaltonPeckPresentation.norm_equivalent)
  refine (pairingLinearMap D).mkContinuous₂ (5 / c ^ 2) ?_
  exact (by
    intro z w
    have hzq : kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤
        ‖z‖ / c := (le_div_iff₀ hdata.1).2 (by
      simpa [mul_comm] using (hdata.2.2 z).1)
    have hwq : kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates w) ≤
        ‖w‖ / c := (le_div_iff₀ hdata.1).2 (by
      simpa [mul_comm] using (hdata.2.2 w).1)
    have hqz : 0 ≤ kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hqw : 0 ≤ kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates w) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      ‖pairingLinearMap D z w‖ = |canonicalPairing
          (canonicalRealKaltonPeckPresentation.coordinates z)
          (canonicalRealKaltonPeckPresentation.coordinates w)| := Real.norm_eq_abs _
      _ ≤ 5 * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) *
          kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates w) :=
        canonicalPairing_bound D _ _
          (canonicalRealKaltonPeckPresentation.coordinates_mem z)
          (canonicalRealKaltonPeckPresentation.coordinates_mem w)
      _ ≤ 5 * (‖z‖ / c) * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates w) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hzq (by norm_num)) hqw
      _ ≤ 5 * (‖z‖ / c) * (‖w‖ / c) := by
        exact mul_le_mul_of_nonneg_left hwq
          (mul_nonneg (by norm_num) (div_nonneg (norm_nonneg _) hdata.1.le))
      _ = (5 / c ^ 2) * ‖z‖ * ‖w‖ := by field_simp)

private theorem fromL2SquareSummable (x : L2) : IsSquareSummable (fun n ↦ x n) :=
  (memlpTwoIff (fun n ↦ x n)).1 x.2

private theorem centralizer_zeroS : centralizer (0 : ℕ → ℝ) = 0 := by
  funext n
  simp [centralizer]

/-- The coordinate pair representing the Hilbert-space inclusion into the first coordinate. -/
def kernelPair (x : L2) : (ℕ → ℝ) × (ℕ → ℝ) :=
  ((fun n ↦ x n), 0)

private def sectionPair (x : L2) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (centralizer (fun n ↦ x n), fun n ↦ x n)

private theorem kernelPair_mem (x : L2) : IsAdmissiblePair (kernelPair x) := by
  rw [IsAdmissiblePair]
  constructor
  · simp [kernelPair, IsSquareSummable]
  · simpa [kernelPair, centralizer_zeroS] using fromL2SquareSummable x

private theorem sectionPair_mem (x : L2) : IsAdmissiblePair (sectionPair x) := by
  rw [IsAdmissiblePair]
  constructor
  · exact fromL2SquareSummable x
  · simp [sectionPair, IsSquareSummable]

/-- The canonical vector with the given Hilbert-space first coordinate and zero second coordinate. -/
def kernelVector (x : L2) : CanonicalRealKaltonPeck :=
  Classical.choose (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (kernelPair x) (by exact kernelPair_mem x))

private theorem kernelVector_coordinates (x : L2) :
    canonicalRealKaltonPeckPresentation.coordinates (kernelVector x) = kernelPair x :=
  Classical.choose_spec (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (kernelPair x) (by exact kernelPair_mem x))

private def sectionVector (x : L2) : CanonicalRealKaltonPeck :=
  Classical.choose (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (sectionPair x) (sectionPair_mem x))

private theorem sectionVector_coordinates (x : L2) :
    canonicalRealKaltonPeckPresentation.coordinates (sectionVector x) = sectionPair x :=
  Classical.choose_spec (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (sectionPair x) (sectionPair_mem x))

/-- The first-coordinate Hilbert-space inclusion as a linear map. -/
def kernelLinearMap : L2 →ₗ[ℝ] CanonicalRealKaltonPeck :=
  { toFun := kernelVector
    map_add' := by
      intro x y
      apply canonicalRealKaltonPeckPresentation.coordinates_injective
      calc
        canonicalRealKaltonPeckPresentation.coordinates (kernelVector (x + y)) =
            kernelPair (x + y) := kernelVector_coordinates (x + y)
        _ = kernelPair x + kernelPair y := by
          apply Prod.ext
          · rfl
          · simp [kernelPair]
        _ = canonicalRealKaltonPeckPresentation.coordinates (kernelVector x) +
            canonicalRealKaltonPeckPresentation.coordinates (kernelVector y) := by
          rw [kernelVector_coordinates, kernelVector_coordinates]
        _ = canonicalRealKaltonPeckPresentation.coordinates (kernelVector x + kernelVector y) :=
          (canonicalRealKaltonPeckPresentation.coordinates.map_add _ _).symm
    map_smul' := by
      intro c x
      apply canonicalRealKaltonPeckPresentation.coordinates_injective
      calc
        canonicalRealKaltonPeckPresentation.coordinates (kernelVector (c • x)) =
            kernelPair (c • x) := kernelVector_coordinates (c • x)
        _ = c • kernelPair x := by
          apply Prod.ext
          · rfl
          · simp [kernelPair]
        _ = c • canonicalRealKaltonPeckPresentation.coordinates (kernelVector x) := by
          rw [kernelVector_coordinates]
        _ = canonicalRealKaltonPeckPresentation.coordinates (c • kernelVector x) := by
          rw [map_smul]
          }

/-- The bounded first-coordinate Hilbert-space inclusion. -/
def kernelContinuousLinearMap : L2 →L[ℝ] CanonicalRealKaltonPeck := by
  let C : ℝ := Classical.choose
    (Classical.choose_spec canonicalRealKaltonPeckPresentation.norm_equivalent)
  let c : ℝ := Classical.choose canonicalRealKaltonPeckPresentation.norm_equivalent
  have hdata : 0 < c ∧ 0 < C ∧ ∀ z,
      c * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤ ‖z‖ ∧
        ‖z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates z) :=
    Classical.choose_spec (Classical.choose_spec
      canonicalRealKaltonPeckPresentation.norm_equivalent)
  refine kernelLinearMap.mkContinuous C ?_
  exact (by
    intro x
    calc
      ‖kernelLinearMap x‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates (kernelLinearMap x)) :=
        (hdata.2.2 _).2
      _ = C * l2Norm (fun n ↦ x n) := by
        change C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates (kernelVector x)) = _
        rw [kernelVector_coordinates]
        change C * (l2Norm ((fun n ↦ x n) - centralizer 0) + l2Norm 0) = _
        rw [centralizer_zeroS]
        simp [l2Norm]
      _ = C * ‖x‖ := by
        rw [l2Norm_toL2 _ (fromL2SquareSummable x)]
        congr 1)

private theorem sectionVector_norm_bound (x : L2) :
    ‖sectionVector x‖ ≤
      Classical.choose (Classical.choose_spec
        canonicalRealKaltonPeckPresentation.norm_equivalent) * ‖x‖ := by
  let C : ℝ := Classical.choose
    (Classical.choose_spec canonicalRealKaltonPeckPresentation.norm_equivalent)
  let c : ℝ := Classical.choose canonicalRealKaltonPeckPresentation.norm_equivalent
  have hdata : 0 < c ∧ 0 < C ∧ ∀ z,
      c * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤ ‖z‖ ∧
        ‖z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates z) :=
    Classical.choose_spec (Classical.choose_spec
      canonicalRealKaltonPeckPresentation.norm_equivalent)
  change ‖sectionVector x‖ ≤ C * ‖x‖
  calc
    ‖sectionVector x‖ ≤ C * kaltonPeckQuasiNorm
        (canonicalRealKaltonPeckPresentation.coordinates (sectionVector x)) :=
      (hdata.2.2 _).2
    _ = C * l2Norm (fun n ↦ x n) := by
      rw [sectionVector_coordinates]
      change C * (l2Norm
        (centralizer (fun n ↦ x n) - centralizer (fun n ↦ x n)) +
          l2Norm (fun n ↦ x n)) = _
      rw [sub_self]
      simp [l2Norm]
    _ = C * ‖x‖ := by
      rw [l2Norm_toL2 _ (fromL2SquareSummable x)]
      congr 1

private theorem pairingContinuousLinearMap_apply (D : StrongPairingData)
    (z w : CanonicalRealKaltonPeck) :
    pairingContinuousLinearMap D z w = canonicalPairing
      (canonicalRealKaltonPeckPresentation.coordinates z)
      (canonicalRealKaltonPeckPresentation.coordinates w) := rfl

private theorem canonicalPairing_kernel_right
    (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : IsAdmissiblePair p) (a : L2) :
    canonicalPairing p (kernelPair a) = -inner ℝ (toL2 p.2 hp.1) a := by
  rw [canonicalPairing, lp.inner_eq_tsum, ← tsum_neg]
  apply tsum_congr
  intro n
  simp [canonicalPairingTerm, kernelPair, toL2]

private theorem canonicalPairing_kernel_left
    (a : L2) (q : (ℕ → ℝ) × (ℕ → ℝ)) (hq : IsAdmissiblePair q) :
    canonicalPairing (kernelPair a) q = inner ℝ a (toL2 q.2 hq.1) := by
  rw [canonicalPairing, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [canonicalPairingTerm, kernelPair, toL2]
  ring

private theorem canonicalPairing_section_right
    (p : (ℕ → ℝ) × (ℕ → ℝ)) (y : L2) :
    canonicalPairing p (sectionPair y) =
      ∑' n, (p.1 n * y n - p.2 n * centralizer (fun k ↦ y k) n) := by
  rw [canonicalPairing]
  apply tsum_congr
  intro n
  simp [canonicalPairingTerm, sectionPair]
  ring

private theorem pairing_kernel_right (D : StrongPairingData) (z : CanonicalRealKaltonPeck)
    (a : L2) : pairingContinuousLinearMap D z (kernelContinuousLinearMap a) =
      -inner ℝ (toL2 (canonicalRealKaltonPeckPresentation.coordinates z).2
        (canonicalRealKaltonPeckPresentation.coordinates_mem z).1) a := by
  rw [pairingContinuousLinearMap_apply]
  change canonicalPairing (canonicalRealKaltonPeckPresentation.coordinates z)
      (canonicalRealKaltonPeckPresentation.coordinates (kernelVector a)) = _
  rw [kernelVector_coordinates]
  exact canonicalPairing_kernel_right _
    (canonicalRealKaltonPeckPresentation.coordinates_mem z) a

private theorem pairing_kernel_left (D : StrongPairingData) (a : L2)
    (z : CanonicalRealKaltonPeck) : pairingContinuousLinearMap D (kernelContinuousLinearMap a) z =
      inner ℝ a (toL2 (canonicalRealKaltonPeckPresentation.coordinates z).2
        (canonicalRealKaltonPeckPresentation.coordinates_mem z).1) := by
  rw [pairingContinuousLinearMap_apply]
  change canonicalPairing
      (canonicalRealKaltonPeckPresentation.coordinates (kernelVector a))
      (canonicalRealKaltonPeckPresentation.coordinates z) = _
  rw [kernelVector_coordinates]
  exact canonicalPairing_kernel_left a _
    (canonicalRealKaltonPeckPresentation.coordinates_mem z)

private theorem pairing_section_right (D : StrongPairingData) (z : CanonicalRealKaltonPeck)
    (y : L2) : pairingContinuousLinearMap D z (sectionVector y) =
      ∑' n, ((canonicalRealKaltonPeckPresentation.coordinates z).1 n * y n -
        (canonicalRealKaltonPeckPresentation.coordinates z).2 n *
          centralizer (fun k ↦ y k) n) := by
  rw [pairingContinuousLinearMap_apply, sectionVector_coordinates]
  exact canonicalPairing_section_right _ y

private theorem pairing_section_kernel (D : StrongPairingData) (b a : L2) :
    pairingContinuousLinearMap D (sectionVector b) (kernelContinuousLinearMap a) =
      -inner ℝ b a := by
  rw [pairing_kernel_right]
  congr 2
  ext n
  exact congr_fun (congr_arg Prod.snd (sectionVector_coordinates b)) n

private theorem pairing_kernel_section (D : StrongPairingData) (a y : L2) :
    pairingContinuousLinearMap D (kernelContinuousLinearMap a) (sectionVector y) =
      inner ℝ a y := by
  rw [pairing_kernel_left]
  congr 1
  ext n
  exact congr_fun (congr_arg Prod.snd (sectionVector_coordinates y)) n

private theorem vector_eq_kernelVector_of_second_eq_zero (z : CanonicalRealKaltonPeck)
    (hz : (canonicalRealKaltonPeckPresentation.coordinates z).2 = 0) :
    ∃ a : L2, z = kernelVector a := by
  have ha : IsSquareSummable (canonicalRealKaltonPeckPresentation.coordinates z).1 := by
    have h := (canonicalRealKaltonPeckPresentation.coordinates_mem z).2
    rw [hz, centralizer_zeroS] at h
    simpa using h
  let a := toL2 (canonicalRealKaltonPeckPresentation.coordinates z).1 ha
  refine ⟨a, ?_⟩
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [kernelVector_coordinates]
  apply Prod.ext
  · rfl
  · exact hz

private theorem functional_zero_of_zero_second
    (f : StrongDual ℝ CanonicalRealKaltonPeck)
    (hf : ∀ a, f (kernelContinuousLinearMap a) = 0)
    (z : CanonicalRealKaltonPeck)
    (hz : (canonicalRealKaltonPeckPresentation.coordinates z).2 = 0) : f z = 0 := by
  obtain ⟨a, rfl⟩ := vector_eq_kernelVector_of_second_eq_zero z hz
  exact hf a

private theorem section_add_defect_second (x y : L2) :
    (canonicalRealKaltonPeckPresentation.coordinates
      (sectionVector (x + y) - sectionVector x - sectionVector y)).2 = 0 := by
  rw [map_sub, map_sub, sectionVector_coordinates, sectionVector_coordinates,
    sectionVector_coordinates]
  funext n
  simp [sectionPair]

private theorem section_smul_defect_second (c : ℝ) (x : L2) :
    (canonicalRealKaltonPeckPresentation.coordinates
      (sectionVector (c • x) - c • sectionVector x)).2 = 0 := by
  rw [map_sub, map_smul, sectionVector_coordinates, sectionVector_coordinates]
  funext n
  simp [sectionPair]

private theorem vector_sub_section_second (z : CanonicalRealKaltonPeck) :
    let y := toL2 (canonicalRealKaltonPeckPresentation.coordinates z).2
      (canonicalRealKaltonPeckPresentation.coordinates_mem z).1
    (canonicalRealKaltonPeckPresentation.coordinates (z - sectionVector y)).2 = 0 := by
  dsimp only
  rw [map_sub, sectionVector_coordinates]
  funext n
  simp [sectionPair, toL2]

private theorem pairing_ker_eq_zero (D : StrongPairingData) (z : CanonicalRealKaltonPeck)
    (hz : pairingContinuousLinearMap D z = 0) : z = 0 := by
  let x := toL2 (canonicalRealKaltonPeckPresentation.coordinates z).2
    (canonicalRealKaltonPeckPresentation.coordinates_mem z).1
  have hxeval := congr_arg
    (fun f : StrongDual ℝ CanonicalRealKaltonPeck ↦ f (kernelContinuousLinearMap x)) hz
  have hinner : inner ℝ x x = 0 := by
    rw [pairing_kernel_right] at hxeval
    change -inner ℝ x x = 0 at hxeval
    exact neg_eq_zero.mp hxeval
  have hxzero : x = 0 := inner_self_eq_zero.mp hinner
  have hsecond : (canonicalRealKaltonPeckPresentation.coordinates z).2 = 0 := by
    funext n
    have hn := congr_arg (fun a : L2 ↦ a n) hxzero
    exact hn
  have hu : IsSquareSummable (canonicalRealKaltonPeckPresentation.coordinates z).1 := by
    have h := (canonicalRealKaltonPeckPresentation.coordinates_mem z).2
    rw [hsecond, centralizer_zeroS] at h
    simpa using h
  let u := toL2 (canonicalRealKaltonPeckPresentation.coordinates z).1 hu
  have hueval := congr_arg
    (fun f : StrongDual ℝ CanonicalRealKaltonPeck ↦ f (sectionVector u)) hz
  have heval : pairingContinuousLinearMap D z (sectionVector u) = inner ℝ u u := by
    rw [pairing_section_right, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp only [u, toL2, RCLike.inner_apply, conj_trivial]
    rw [congr_fun hsecond n]
    simp only [Pi.zero_apply, zero_mul, sub_zero]
  have huinner : inner ℝ u u = 0 := by
    rw [heval] at hueval
    simpa using hueval
  have huzero : u = 0 := inner_self_eq_zero.mp huinner
  have hfirst : (canonicalRealKaltonPeckPresentation.coordinates z).1 = 0 := by
    funext n
    have hn := congr_arg (fun a : L2 ↦ a n) huzero
    exact hn
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [map_zero]
  apply Prod.ext
  · exact hfirst
  · exact hsecond

private theorem pairing_injective (D : StrongPairingData) :
    Function.Injective (pairingContinuousLinearMap D) := by
  intro z z' h
  rw [← sub_eq_zero]
  apply pairing_ker_eq_zero D
  rw [map_sub, h, sub_self]

private theorem pairing_surjective (D : StrongPairingData) :
    Function.Surjective (pairingContinuousLinearMap D) := by
  intro f
  let fj : StrongDual ℝ L2 := f.comp kernelContinuousLinearMap
  let zrep : L2 := (InnerProductSpace.toDual ℝ L2).symm fj
  let b : L2 := -zrep
  let p0 : CanonicalRealKaltonPeck := sectionVector b
  let residual : StrongDual ℝ CanonicalRealKaltonPeck :=
    f - pairingContinuousLinearMap D p0
  have hriesz (a : L2) : inner ℝ zrep a = f (kernelContinuousLinearMap a) := by
    change inner ℝ ((InnerProductSpace.toDual ℝ L2).symm fj) a = fj a
    exact InnerProductSpace.toDual_symm_apply
  have hresidual_kernel (a : L2) : residual (kernelContinuousLinearMap a) = 0 := by
    change f (kernelContinuousLinearMap a) -
      pairingContinuousLinearMap D (sectionVector b) (kernelContinuousLinearMap a) = 0
    rw [pairing_section_kernel]
    rw [← hriesz a]
    simp [b]
  let gLinear : L2 →ₗ[ℝ] ℝ :=
    { toFun := fun y ↦ residual (sectionVector y)
      map_add' := by
        intro x y
        have hz := functional_zero_of_zero_second residual hresidual_kernel
          (sectionVector (x + y) - sectionVector x - sectionVector y)
          (section_add_defect_second x y)
        rw [map_sub, map_sub] at hz
        linarith
      map_smul' := by
        intro c x
        have hz := functional_zero_of_zero_second residual hresidual_kernel
          (sectionVector (c • x) - c • sectionVector x)
          (section_smul_defect_second c x)
        rw [map_sub, map_smul] at hz
        simpa only [RingHom.id_apply, sub_eq_zero] using hz }
  let C : ℝ := Classical.choose
    (Classical.choose_spec canonicalRealKaltonPeckPresentation.norm_equivalent)
  let c : ℝ := Classical.choose canonicalRealKaltonPeckPresentation.norm_equivalent
  have hdata : 0 < c ∧ 0 < C ∧ ∀ z,
      c * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤ ‖z‖ ∧
        ‖z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates z) :=
    Classical.choose_spec (Classical.choose_spec
      canonicalRealKaltonPeckPresentation.norm_equivalent)
  let g : StrongDual ℝ L2 := gLinear.mkContinuous (‖residual‖ * C) (by
    intro y
    calc
      ‖gLinear y‖ = ‖residual (sectionVector y)‖ := rfl
      _ ≤ ‖residual‖ * ‖sectionVector y‖ := residual.le_opNorm _
      _ ≤ ‖residual‖ * (C * ‖y‖) :=
        mul_le_mul_of_nonneg_left (sectionVector_norm_bound y) (norm_nonneg _)
      _ = (‖residual‖ * C) * ‖y‖ := by ring)
  let a : L2 := (InnerProductSpace.toDual ℝ L2).symm g
  have hg (y : L2) : inner ℝ a y = residual (sectionVector y) := by
    change inner ℝ ((InnerProductSpace.toDual ℝ L2).symm g) y = g y
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨p0 + kernelContinuousLinearMap a, ?_⟩
  ext v
  let y := toL2 (canonicalRealKaltonPeckPresentation.coordinates v).2
    (canonicalRealKaltonPeckPresentation.coordinates_mem v).1
  have hzero := functional_zero_of_zero_second residual hresidual_kernel
    (v - sectionVector y) (vector_sub_section_second v)
  rw [map_sub] at hzero
  have hresidual : residual v = inner ℝ a y := by
    calc
      residual v = residual (sectionVector y) := sub_eq_zero.mp hzero
      _ = inner ℝ a y := (hg y).symm
  change pairingContinuousLinearMap D (p0 + kernelContinuousLinearMap a) v = f v
  rw [map_add]
  change pairingContinuousLinearMap D p0 v +
    pairingContinuousLinearMap D (kernelContinuousLinearMap a) v = f v
  rw [pairing_kernel_left]
  change pairingContinuousLinearMap D p0 v + inner ℝ a y = f v
  change f v - pairingContinuousLinearMap D p0 v = inner ℝ a y at hresidual
  linarith

/-- The strong symplectic form obtained from the proved coordinate-pairing bounds. -/
def strongFormOfData (D : StrongPairingData) :
    StrongSymplecticForm CanonicalRealKaltonPeck := by
  let e : CanonicalRealKaltonPeck ≃L[ℝ] StrongDual ℝ CanonicalRealKaltonPeck :=
    ContinuousLinearEquiv.ofBijective (pairingContinuousLinearMap D)
      (by exact LinearMap.ker_eq_bot.mpr (pairing_injective D))
      (by exact LinearMap.range_eq_top.mpr (pairing_surjective D))
  refine { toDual := e, alternating := ?_ }
  exact (by
    intro z
    change pairingContinuousLinearMap D z z = 0
    rw [pairingContinuousLinearMap_apply, canonicalPairing]
    have hzero : canonicalPairingTerm
        (canonicalRealKaltonPeckPresentation.coordinates z)
        (canonicalRealKaltonPeckPresentation.coordinates z) = 0 := by
      funext n
      simp [canonicalPairingTerm]
    rw [hzero]
    exact tsum_zero)


/-- The standard unit vector in the real sequence space.
Support definition for blueprint label `thm:ks-primary`. -/
def standardBasisSequence (n : ℕ) : ℕ → ℝ := by
  exact fun k ↦ if k = n then 1 else 0

/-- The canonical vector with coordinates `(eₙ, 0)`.
Support definition for blueprint labels `thm:ks-primary` and `thm:block-primary`. -/
def canonicalFirstBasisVector (n : ℕ) : CanonicalRealKaltonPeck := by
  refine ⟨(standardBasisSequence n, 0), ?_⟩
  simp only [IsAdmissiblePair]
  constructor
  · simp [IsSquareSummable]
  · apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton n).subset ?_
    intro k hk
    by_cases hkn : k = n
    · simp [hkn]
    · simp [Function.mem_support, standardBasisSequence, centralizer, hkn] at hk

/-- The canonical vector with coordinates `(0, eₙ)`.
Support definition for blueprint labels `thm:ks-primary` and `thm:block-primary`. -/
def canonicalSecondBasisVector (n : ℕ) : CanonicalRealKaltonPeck := by
  refine ⟨(0, standardBasisSequence n), ?_⟩
  have hsquare : IsSquareSummable (standardBasisSequence n) := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton n).subset ?_
    intro k hk
    by_cases hkn : k = n
    · simp [hkn]
    · simp [Function.mem_support, standardBasisSequence, hkn] at hk
  have hl2 : l2Norm (standardBasisSequence n) = 1 := by
    rw [l2Norm, tsum_eq_single n]
    · simp [standardBasisSequence]
    · intro k hk
      simp [standardBasisSequence, hk]
  have hcentral : centralizer (standardBasisSequence n) = 0 := by
    funext k
    by_cases hk : k = n
    · simp [centralizer, standardBasisSequence, hk, hl2]
    · simp [centralizer, standardBasisSequence, hk]
  rw [IsAdmissiblePair]
  constructor
  · exact hsquare
  · rw [hcentral]
    simp [IsSquareSummable]

/-- The two canonical coordinate-generator identities.
Support declaration for blueprint labels `thm:ks-primary` and `thm:block-primary`. -/
theorem canonicalBasisCoordinates (n : ℕ) :
    canonicalRealKaltonPeckPresentation.coordinates (canonicalFirstBasisVector n) =
        (standardBasisSequence n, 0) ∧
      canonicalRealKaltonPeckPresentation.coordinates (canonicalSecondBasisVector n) =
        (0, standardBasisSequence n) := by
  constructor <;> rfl

/-- The canonical inclusion `ℓ₂ → Z₂`, given by the first coordinate.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
def canonicalL2Inclusion : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck := by
  exact kernelContinuousLinearMap

/-- Coordinates of the canonical Hilbert-space inclusion.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2Inclusion_coordinates (x : CanonicalL2) :
    canonicalRealKaltonPeckPresentation.coordinates (canonicalL2Inclusion x) =
      ((fun n ↦ x n), 0) := by
  exact kernelVector_coordinates x

/-- The canonical Hilbert-space inclusion is injective.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2Inclusion_injective :
    Function.Injective canonicalL2Inclusion := by
  intro x y hxy
  have hcoordinates := congrArg canonicalRealKaltonPeckPresentation.coordinates hxy
  rw [canonicalL2Inclusion_coordinates, canonicalL2Inclusion_coordinates] at hcoordinates
  apply Subtype.ext
  exact congrArg Prod.fst hcoordinates

/-- The canonical Kalton--Peck space is infinite-dimensional.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalRealKaltonPeck_not_finiteDimensional :
    ¬ FiniteDimensional ℝ CanonicalRealKaltonPeck := by
  intro h
  let : FiniteDimensional ℝ CanonicalRealKaltonPeck := h
  have hL2 : FiniteDimensional ℝ CanonicalL2 :=
    FiniteDimensional.of_injective canonicalL2Inclusion.toLinearMap
      canonicalL2Inclusion_injective
  exact canonicalL2_not_finiteDimensional hL2

/-- The canonical inclusion identifies `ℓ₂` with the kernel of the canonical quotient.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2Inclusion_range :
    canonicalL2Inclusion.range = canonicalL2Quotient.ker := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    change canonicalL2Quotient (canonicalL2Inclusion x) = 0
    apply Subtype.ext
    funext n
    rw [canonicalL2Quotient_apply, canonicalL2Inclusion_coordinates]
    rfl
  · intro z hz
    change canonicalL2Quotient z = 0 at hz
    have hsecond :
        (canonicalRealKaltonPeckPresentation.coordinates z).2 = 0 := by
      funext n
      have hn := congrArg (fun y : CanonicalL2 ↦ y n) hz
      simpa only [canonicalL2Quotient_apply, lp.coeFn_zero, Pi.zero_apply] using hn
    obtain ⟨x, hx⟩ := vector_eq_kernelVector_of_second_eq_zero z hsecond
    refine ⟨x, ?_⟩
    exact hx.symm

/-- The strong Kalton--Swanson form on the fixed project-normalized canonical model.
Blueprint label: `thm:ks-primary`; audit IDs `EXT-KS-PRIMARY` and `INF-KP-L2-PAIRING`. -/
def canonicalKaltonSwansonForm : StrongSymplecticForm CanonicalRealKaltonPeck := by
  exact strongFormOfData (by exact strongPairingData)

/-- On finite-coordinate vectors, the canonical form is the single combined coordinate sum.
Blueprint label: `thm:ks-primary`; audit IDs `EXT-KS-PRIMARY`, `INF-KP-L2-PAIRING`, and
`BLK-KS-PAIRING`. -/
theorem canonicalKaltonSwansonForm_finite_coordinates
    (z w : CanonicalRealKaltonPeck)
    (_hz : IsFiniteCoordinatePair (canonicalRealKaltonPeckPresentation.coordinates z))
    (_hw : IsFiniteCoordinatePair (canonicalRealKaltonPeckPresentation.coordinates w)) :
    canonicalKaltonSwansonForm.toDual z w =
      ∑' n : ℕ,
        ((canonicalRealKaltonPeckPresentation.coordinates z).1 n *
            (canonicalRealKaltonPeckPresentation.coordinates w).2 n -
          (canonicalRealKaltonPeckPresentation.coordinates w).1 n *
            (canonicalRealKaltonPeckPresentation.coordinates z).2 n) := by
  rfl

/-- The Kalton--Swanson form transported to an arbitrary complete presented model.
Blueprint label: `thm:ks-transport`; audit ID `EXT-KS-STRONG`. -/
def transportedKaltonSwansonForm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) : StrongSymplecticForm X := by
  let e := presentationEquiv hX canonicalRealKaltonPeckPresentation
  let dualELinear : StrongDual ℝ CanonicalRealKaltonPeck ≃ₗ[ℝ] StrongDual ℝ X :=
    { toFun := transpose e.toContinuousLinearMap
      invFun := transpose e.symm.toContinuousLinearMap
      left_inv := by
        intro f
        ext y
        simp [transpose, e]
      right_inv := by
        intro f
        ext x
        simp [transpose, e]
      map_add' := (transpose e.toContinuousLinearMap).map_add
      map_smul' := (transpose e.toContinuousLinearMap).map_smul }
  let dualE : StrongDual ℝ CanonicalRealKaltonPeck ≃L[ℝ] StrongDual ℝ X :=
    ContinuousLinearEquiv.mk dualELinear
      (transpose e.toContinuousLinearMap).continuous
      (transpose e.symm.toContinuousLinearMap).continuous
  refine
    { toDual := e.trans (canonicalKaltonSwansonForm.toDual.trans dualE)
      alternating := ?_ }
  intro x
  exact canonicalKaltonSwansonForm.alternating (e x)

/-- The transported form is the pullback of the canonical form along the coordinate equivalence.
Blueprint label: `thm:ks-transport`; audit IDs `EXT-KS-STRONG` and
`INF-KP-COORDINATE-EQUIVALENCE`. -/
theorem transportedKaltonSwansonForm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (x y : X) :
    (transportedKaltonSwansonForm hX).toDual x y =
      canonicalKaltonSwansonForm.toDual
        (presentationEquiv hX canonicalRealKaltonPeckPresentation x)
        (presentationEquiv hX canonicalRealKaltonPeckPresentation y) := by
  rfl

/-- A successive normalized block sequence of finitely supported real `ℓ₂` vectors.
Blueprint label: `thm:block-primary`; audit ID `RES-BLOCK-OPERATOR-IDENTITIES`. -/
def IsSuccessiveNormalizedBlockSequence (w : ℕ → ℕ → ℝ) : Prop := by
  exact (∀ n, Set.Finite {k | w n k ≠ 0} ∧ Set.Nonempty {k | w n k ≠ 0}) ∧
    (∀ n, l2Norm (w n) = 1) ∧
      ∀ n i j, w n i ≠ 0 → w (n + 1) j ≠ 0 → i < j

/-- Every support in one block family is disjoint from every support in the other.
Blueprint labels: `thm:block-primary` and `thm:block-transport`. -/
def AreMutuallySupportDisjoint (w v : ℕ → ℕ → ℝ) : Prop := by
  exact ∀ n m, Disjoint {k | w n k ≠ 0} {k | v m k ≠ 0}

private theorem blockSquareSummable (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (n : ℕ) :
    IsSquareSummable (w n) := by
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact hw.1 n |>.1.subset (by simp)

/-- One normalized block viewed as a Hilbert-space vector. -/
def blockL2 (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (n : ℕ) :
    lp (fun _ : ℕ ↦ ℝ) 2 :=
  toL2 (w n) (by exact blockSquareSummable w hw n)

private theorem blockSupportBefore (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) {n m : ℕ} (hnm : n < m)
    {i j : ℕ} (hi : w n i ≠ 0) (hj : w m j ≠ 0) : i < j := by
  revert j
  induction m, hnm using Nat.le_induction with
  | base =>
      intro j hj
      exact hw.2.2 n i j hi hj
  | succ m hnm ih =>
      intro j hj
      obtain ⟨k, hk⟩ := hw.1 m |>.2
      change w m k ≠ 0 at hk
      exact lt_trans (ih hk) (hw.2.2 m k j hk hj)

private theorem blockSupportDisjoint (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) {n m : ℕ} (hnm : n ≠ m) :
    Disjoint {k | w n k ≠ 0} {k | w m k ≠ 0} := by
  rw [Set.disjoint_left]
  intro k hkn hkm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact Nat.lt_asymm (blockSupportBefore w hw hlt hkn hkm)
      (blockSupportBefore w hw hlt hkn hkm)
  · exact Nat.lt_asymm (blockSupportBefore w hw hgt hkm hkn)
      (blockSupportBefore w hw hgt hkm hkn)

private theorem blocksOrthonormal (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    Orthonormal ℝ (blockL2 w hw) := by
  rw [orthonormal_iff_ite]
  intro n m
  by_cases hnm : n = m
  · subst m
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K]
    change ‖toL2 (w n) (by exact blockSquareSummable w hw n)‖ ^ 2 = 1
    rw [← l2Norm_toL2 (w n) (by exact blockSquareSummable w hw n), hw.2.1]
    norm_num
  · rw [ite_eq_right hnm, lp.inner_eq_tsum]
    have hzfun : (fun k ↦ inner ℝ (blockL2 w hw n k) (blockL2 w hw m k)) =
        (0 : ℕ → ℝ) := by
      funext k
      simp only [RCLike.inner_apply, conj_trivial, blockL2, toL2, Pi.zero_apply]
      have hz : w n k = 0 ∨ w m k = 0 := by
        by_contra h
        push Not at h
        exact Set.disjoint_left.1 (blockSupportDisjoint w hw hnm) h.1 h.2
      rcases hz with hz | hz <;> simp [hz]
    rw [hzfun]
    exact tsum_zero

/-- The Hilbert-space isometry induced by the orthonormal successive blocks. -/
def blockIsometry (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    lp (fun _ : ℕ ↦ ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  (show Orthonormal ℝ (blockL2 w hw) from by
    exact blocksOrthonormal w hw).orthogonalFamily.linearIsometry

/-- A coordinate lies in the support of at least one block. -/
def HasActiveBlock (w : ℕ → ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ n, w n k ≠ 0

/-- The index of the block active at a coordinate, defaulting to zero off the block supports. -/
def activeBlockIndex (w : ℕ → ℕ → ℝ) (k : ℕ) : ℕ :=
  if hk : HasActiveBlock w k then Classical.choose hk else 0

private theorem activeBlockIndex_spec (w : ℕ → ℕ → ℝ) {k : ℕ}
    (hk : HasActiveBlock w k) : w (activeBlockIndex w k) k ≠ 0 := by
  rw [activeBlockIndex, dite_eq_left hk]
  exact Classical.choose_spec hk

private theorem activeBlockIndex_eq (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) {n k : ℕ} (hnk : w n k ≠ 0) :
    activeBlockIndex w k = n := by
  have hk : HasActiveBlock w k := ⟨n, hnk⟩
  by_contra hne
  exact Set.disjoint_left.1 (blockSupportDisjoint w hw hne)
    (activeBlockIndex_spec w hk) hnk

/-- Replace each sequence coordinate by its coefficient on the corresponding block. -/
def rawBlockTransform (w : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if _hk : HasActiveBlock w k then
    x (activeBlockIndex w k) * w (activeBlockIndex w k) k
  else 0

private theorem rawBlockTransform_apply_of_mem (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : ℕ → ℝ)
    {n k : ℕ} (hnk : w n k ≠ 0) : rawBlockTransform w x k = x n * w n k := by
  rw [rawBlockTransform, dite_eq_left ⟨n, hnk⟩, activeBlockIndex_eq w hw hnk]

private theorem rawBlockTransform_apply_of_not_mem (w : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ) {k : ℕ} (hk : ¬ HasActiveBlock w k) :
    rawBlockTransform w x k = 0 := by
  rw [rawBlockTransform, dite_eq_right hk]

private theorem rawBlockTransform_add (w : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) :
    rawBlockTransform w (x + y) = rawBlockTransform w x + rawBlockTransform w y := by
  funext k
  by_cases hk : HasActiveBlock w k
  · simp [rawBlockTransform, hk, add_mul]
  · simp [rawBlockTransform, hk]

private theorem rawBlockTransform_smul (w : ℕ → ℕ → ℝ) (a : ℝ)
    (x : ℕ → ℝ) : rawBlockTransform w (a • x) = a • rawBlockTransform w x := by
  funext k
  by_cases hk : HasActiveBlock w k
  · simp [rawBlockTransform, hk, mul_assoc]
  · simp [rawBlockTransform, hk]

private lemma rawBlockTransform_zero (w : ℕ → ℕ → ℝ) :
    rawBlockTransform w 0 = 0 := by
  funext k
  simp [rawBlockTransform]

private theorem rawBlockTransform_sub (w : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) :
    rawBlockTransform w (x - y) = rawBlockTransform w x - rawBlockTransform w y := by
  rw [sub_eq_add_neg, rawBlockTransform_add]
  have hneg : rawBlockTransform w (-y) = -rawBlockTransform w y := by
    simpa only [neg_one_smul] using rawBlockTransform_smul w (-1) y
  rw [hneg, sub_eq_add_neg]

private theorem rawBlockTransform_eq_isometry (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : ℕ → ℝ)
    (hx : IsSquareSummable x) :
    rawBlockTransform w x = blockIsometry w hw (toL2 x hx) := by
  funext k
  have hs := (blocksOrthonormal w hw).orthogonalFamily.hasSum_linearIsometry (toL2 x hx)
  have hsk := (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 2 k).hasSum hs
  have hsum : HasSum (fun n ↦ x n * w n k) (blockIsometry w hw (toL2 x hx) k) := by
    have hsk' : HasSum (fun n ↦ x n * w n k)
        ((show Orthonormal ℝ (blockL2 w hw) from by
    exact blocksOrthonormal w hw).orthogonalFamily.linearIsometry (toL2 x hx) k) := by
      apply hsk.congr
      intro s
      apply Finset.sum_congr rfl
      intro n hn
      change x n * w n k = x n * w n k
      rfl
    simpa [blockIsometry] using hsk'
  rw [← hsum.tsum_eq]
  by_cases hk : HasActiveBlock w k
  · rw [rawBlockTransform, dite_eq_left hk, tsum_eq_single (activeBlockIndex w k)]
    intro n hne
    have hz : w n k = 0 := by
      by_contra hn
      exact hne (activeBlockIndex_eq w hw hn).symm
    simp [hz]
  · rw [rawBlockTransform, dite_eq_right hk]
    symm
    calc
      (∑' n, x n * w n k) = ∑' _n, 0 := by
        apply tsum_congr
        intro n
        have hwn : w n k = 0 := by
          by_contra hn
          exact hk ⟨n, hn⟩
        simp [hwn]
      _ = 0 := tsum_zero

private theorem rawBlockTransform_squareSummable (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : ℕ → ℝ)
    (hx : IsSquareSummable x) : IsSquareSummable (rawBlockTransform w x) := by
  rw [← memlpTwoIff]
  rw [rawBlockTransform_eq_isometry w hw x hx]
  exact lp.memℓp _

private theorem rawBlockTransform_l2Norm (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : ℕ → ℝ)
    (hx : IsSquareSummable x) :
    l2Norm (rawBlockTransform w x) = l2Norm x := by
  let hBx := rawBlockTransform_squareSummable w hw x hx
  rw [l2Norm_toL2 (rawBlockTransform w x) hBx, l2Norm_toL2 x hx]
  have heq : toL2 (rawBlockTransform w x) hBx = blockIsometry w hw (toL2 x hx) := by
    ext k
    exact congr_fun (rawBlockTransform_eq_isometry w hw x hx) k
  rw [heq]
  exact LinearIsometry.norm_map _ _

/-- The centralizer correction associated with the block transform. -/
def rawBlockCorrection (w : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if _hk : HasActiveBlock w k then
    x (activeBlockIndex w k) * centralizer (w (activeBlockIndex w k)) k
  else 0

private theorem rawBlockCorrection_add (w : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) :
    rawBlockCorrection w (x + y) = rawBlockCorrection w x + rawBlockCorrection w y := by
  funext k
  by_cases hk : HasActiveBlock w k
  · simp [rawBlockCorrection, hk, add_mul]
  · simp [rawBlockCorrection, hk]

private theorem rawBlockCorrection_smul (w : ℕ → ℕ → ℝ) (a : ℝ)
    (x : ℕ → ℝ) : rawBlockCorrection w (a • x) = a • rawBlockCorrection w x := by
  funext k
  by_cases hk : HasActiveBlock w k
  · simp [rawBlockCorrection, hk, mul_assoc]
  · simp [rawBlockCorrection, hk]

private lemma rawBlockCorrection_zero (w : ℕ → ℕ → ℝ) :
    rawBlockCorrection w 0 = 0 := by
  funext k
  simp [rawBlockCorrection]

private lemma rawBlockTransform_standardBasis (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (n : ℕ) :
    rawBlockTransform w (standardBasisSequence n) = w n := by
  funext k
  by_cases hk : HasActiveBlock w k
  · rw [rawBlockTransform, dite_eq_left hk]
    by_cases hindex : activeBlockIndex w k = n
    · simp [standardBasisSequence, hindex]
    · have hwn : w n k = 0 := by
        by_contra hn
        exact hindex (activeBlockIndex_eq w hw hn)
      simp [standardBasisSequence, hindex, hwn]
  · have hwn : w n k = 0 := by
      by_contra hn
      exact hk ⟨n, hn⟩
    simp [rawBlockTransform, hk, hwn]

private lemma rawBlockCorrection_standardBasis (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (n : ℕ) :
    rawBlockCorrection w (standardBasisSequence n) = centralizer (w n) := by
  funext k
  by_cases hk : HasActiveBlock w k
  · rw [rawBlockCorrection, dite_eq_left hk]
    by_cases hindex : activeBlockIndex w k = n
    · simp [standardBasisSequence, hindex]
    · have hwn : w n k = 0 := by
        by_contra hn
        exact hindex (activeBlockIndex_eq w hw hn)
      simp [standardBasisSequence, centralizer, hindex, hwn]
  · have hwn : w n k = 0 := by
      by_contra hn
      exact hk ⟨n, hn⟩
    simp [rawBlockCorrection, centralizer, hk, hwn]

private theorem l2Norm_ne_zero_of_apply_ne_zero (x : ℕ → ℝ) (hx : IsSquareSummable x)
    {n : ℕ} (hn : x n ≠ 0) : l2Norm x ≠ 0 := by
  rw [l2Norm_toL2 x hx]
  intro hnorm
  have hz : toL2 x hx = 0 := norm_eq_zero.mp hnorm
  have := congr_arg (fun z : lp (fun _ : ℕ ↦ ℝ) 2 ↦ z n) hz
  exact hn (by simpa [toL2] using this)

private theorem centralizer_rawBlockTransform (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : ℕ → ℝ)
    (hx : IsSquareSummable x) :
    centralizer (rawBlockTransform w x) =
      rawBlockTransform w (centralizer x) + rawBlockCorrection w x := by
  funext k
  change centralizer (rawBlockTransform w x) k =
    rawBlockTransform w (centralizer x) k + rawBlockCorrection w x k
  by_cases hk : HasActiveBlock w k
  · let n := activeBlockIndex w k
    have hwn : w n k ≠ 0 := activeBlockIndex_spec w hk
    have hB := rawBlockTransform_apply_of_mem w hw x hwn
    have hBK := rawBlockTransform_apply_of_mem w hw (centralizer x) hwn
    have hnormB := rawBlockTransform_l2Norm w hw x hx
    rw [centralizer, hB, hnormB, hBK, rawBlockCorrection, dite_eq_left hk]
    change 2 * (x n * w n k) * Real.log (|x n * w n k| / l2Norm x) =
      2 * x n * Real.log (|x n| / l2Norm x) * w n k +
        x n * (2 * w n k * Real.log (|w n k| / l2Norm (w n)))
    rw [hw.2.1 n, div_one]
    by_cases hxn : x n = 0
    · simp [hxn]
    have hnormx : l2Norm x ≠ 0 := l2Norm_ne_zero_of_apply_ne_zero x hx hxn
    have habsxn : |x n| ≠ 0 := abs_ne_zero.mpr hxn
    have habswn : |w n k| ≠ 0 := abs_ne_zero.mpr hwn
    have hdiv : |x n| / l2Norm x ≠ 0 := div_ne_zero habsxn hnormx
    rw [abs_mul, show |x n| * |w n k| / l2Norm x =
      (|x n| / l2Norm x) * |w n k| by field_simp]
    rw [Real.log_mul hdiv habswn]
    ring
  · have hBw : rawBlockTransform w x k = 0 := rawBlockTransform_apply_of_not_mem w x hk
    have hBKw : rawBlockTransform w (centralizer x) k = 0 :=
      rawBlockTransform_apply_of_not_mem w (centralizer x) hk
    simp [centralizer, hBw, hBKw, rawBlockCorrection, hk]

/-- The pair of transformed coordinates, including the centralizer correction. -/
def blockTargetPair (w : ℕ → ℕ → ℝ)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (rawBlockTransform w p.1 + rawBlockCorrection w p.2, rawBlockTransform w p.2)

private theorem blockTargetPair_add (w : ℕ → ℕ → ℝ)
    (p q : (ℕ → ℝ) × (ℕ → ℝ)) :
    blockTargetPair w (p + q) = blockTargetPair w p + blockTargetPair w q := by
  apply Prod.ext
  · change rawBlockTransform w (p.1 + q.1) + rawBlockCorrection w (p.2 + q.2) =
      (rawBlockTransform w p.1 + rawBlockCorrection w p.2) +
        (rawBlockTransform w q.1 + rawBlockCorrection w q.2)
    rw [rawBlockTransform_add, rawBlockCorrection_add]
    abel
  · exact rawBlockTransform_add w p.2 q.2

private theorem blockTargetPair_smul (w : ℕ → ℕ → ℝ) (a : ℝ)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) :
    blockTargetPair w (a • p) = a • blockTargetPair w p := by
  apply Prod.ext <;> simp [blockTargetPair, rawBlockTransform_smul, rawBlockCorrection_smul]

private theorem blockTargetPair_mem (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : IsAdmissiblePair p) :
    IsAdmissiblePair (blockTargetPair w p) := by
  have hx : IsSquareSummable p.2 := hp.1
  have ha : IsSquareSummable (p.1 - centralizer p.2) := hp.2
  have hBx := rawBlockTransform_squareSummable w hw p.2 hx
  rw [IsAdmissiblePair]
  refine ⟨hBx, ?_⟩
  have hcentral := centralizer_rawBlockTransform w hw p.2 hx
  have hdefect :
      (blockTargetPair w p).1 - centralizer (blockTargetPair w p).2 =
        rawBlockTransform w (p.1 - centralizer p.2) := by
    rw [blockTargetPair]
    simp only
    rw [hcentral, rawBlockTransform_sub]
    abel
  rw [hdefect]
  exact rawBlockTransform_squareSummable w hw _ ha

private theorem blockTargetPair_quasiNorm (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w)
    (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : IsAdmissiblePair p) :
    kaltonPeckQuasiNorm (blockTargetPair w p) = kaltonPeckQuasiNorm p := by
  have hx : IsSquareSummable p.2 := hp.1
  have ha : IsSquareSummable (p.1 - centralizer p.2) := hp.2
  have hcentral := centralizer_rawBlockTransform w hw p.2 hx
  have hdefect :
      (blockTargetPair w p).1 - centralizer (blockTargetPair w p).2 =
        rawBlockTransform w (p.1 - centralizer p.2) := by
    rw [blockTargetPair]
    simp only
    rw [hcentral, rawBlockTransform_sub]
    abel
  rw [kaltonPeckQuasiNorm, hdefect]
  change l2Norm (rawBlockTransform w (p.1 - centralizer p.2)) +
      l2Norm (rawBlockTransform w p.2) = _
  rw [rawBlockTransform_l2Norm w hw _ ha, rawBlockTransform_l2Norm w hw _ hx]
  rfl

/-- The canonical vector with the transformed block coordinates. -/
def blockTargetVector (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (z : CanonicalRealKaltonPeck) :
    CanonicalRealKaltonPeck :=
  Classical.choose (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z))
    (by
      exact blockTargetPair_mem w hw _
        (canonicalRealKaltonPeckPresentation.coordinates_mem z)))

private theorem blockTargetVector_coordinates (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (z : CanonicalRealKaltonPeck) :
    canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw z) =
      blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z) :=
  Classical.choose_spec (canonicalRealKaltonPeckPresentation.coordinates_surjective
    (blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z))
    (by
      exact blockTargetPair_mem w hw _
        (canonicalRealKaltonPeckPresentation.coordinates_mem z)))

/-- The block transformation as a linear map on the canonical Kalton–Peck model. -/
def canonicalBlockLinearMap (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    CanonicalRealKaltonPeck →ₗ[ℝ] CanonicalRealKaltonPeck :=
  { toFun := blockTargetVector w hw
    map_add' := by
      intro z z'
      apply canonicalRealKaltonPeckPresentation.coordinates_injective
      calc
        canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw (z + z')) =
            blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates (z + z')) :=
          blockTargetVector_coordinates w hw (z + z')
        _ = blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z +
            canonicalRealKaltonPeckPresentation.coordinates z') := by rw [map_add]
        _ = blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z) +
            blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z') :=
          blockTargetPair_add w _ _
        _ = canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw z) +
            canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw z') := by
          rw [blockTargetVector_coordinates, blockTargetVector_coordinates]
        _ = canonicalRealKaltonPeckPresentation.coordinates
            (blockTargetVector w hw z + blockTargetVector w hw z') :=
          (canonicalRealKaltonPeckPresentation.coordinates.map_add _ _).symm
    map_smul' := by
      intro a z
      apply canonicalRealKaltonPeckPresentation.coordinates_injective
      calc
        canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw (a • z)) =
            blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates (a • z)) :=
          blockTargetVector_coordinates w hw (a • z)
        _ = blockTargetPair w (a • canonicalRealKaltonPeckPresentation.coordinates z) := by
          rw [map_smul]
        _ = a • blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z) :=
          blockTargetPair_smul w a _
        _ = a • canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw z) := by
          rw [blockTargetVector_coordinates]
        _ = canonicalRealKaltonPeckPresentation.coordinates (a • blockTargetVector w hw z) := by
          rw [map_smul]
          }

private theorem canonicalBlockLinearMap_quasiNorm (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (z : CanonicalRealKaltonPeck) :
    kaltonPeckQuasiNorm
        (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockLinearMap w hw z)) =
      kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) := by
  change kaltonPeckQuasiNorm
      (canonicalRealKaltonPeckPresentation.coordinates (blockTargetVector w hw z)) = _
  rw [blockTargetVector_coordinates]
  exact blockTargetPair_quasiNorm w hw _
    (canonicalRealKaltonPeckPresentation.coordinates_mem z)

/-- The canonical block operator associated to a successive normalized block sequence.
Blueprint label: `thm:block-primary`; audit IDs `EXT-K-BLOCK` and
`RES-BLOCK-OPERATOR-IDENTITIES`. -/
def canonicalBlockOperator (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck := by
  let c : ℝ := Classical.choose canonicalRealKaltonPeckPresentation.norm_equivalent
  let C : ℝ := Classical.choose
    (Classical.choose_spec canonicalRealKaltonPeckPresentation.norm_equivalent)
  have hdata : 0 < c ∧ 0 < C ∧ ∀ z,
      c * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤ ‖z‖ ∧
        ‖z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates z) :=
    Classical.choose_spec (Classical.choose_spec
      canonicalRealKaltonPeckPresentation.norm_equivalent)
  refine (canonicalBlockLinearMap w hw).mkContinuous (C / c) ?_
  exact (by
    intro z
    have hq : kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) ≤
        ‖z‖ / c := (le_div_iff₀ hdata.1).2 (by
      simpa [mul_comm] using (hdata.2.2 z).1)
    calc
      ‖canonicalBlockLinearMap w hw z‖ ≤ C * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockLinearMap w hw z)) :=
        (hdata.2.2 _).2
      _ = C * kaltonPeckQuasiNorm (canonicalRealKaltonPeckPresentation.coordinates z) := by
        rw [canonicalBlockLinearMap_quasiNorm]
      _ ≤ C * (‖z‖ / c) := mul_le_mul_of_nonneg_left hq hdata.2.1.le
      _ = (C / c) * ‖z‖ := by ring)

/-- The Hilbert-space isometry induced by a successive normalized block family.
Blueprint support for `thm:block-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
def canonicalL2BlockEmbedding (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) : CanonicalL2 →L[ℝ] CanonicalL2 :=
  (blockIsometry w hw).toContinuousLinearMap

/-- A canonical Hilbert block embedding preserves norms.
Blueprint support for `thm:block-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2BlockEmbedding_norm (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x : CanonicalL2) :
    ‖canonicalL2BlockEmbedding w hw x‖ = ‖x‖ := by
  exact (blockIsometry w hw).norm_map x

/-- A canonical Hilbert block embedding is injective.
Blueprint support for `thm:block-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2BlockEmbedding_injective (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    Function.Injective (canonicalL2BlockEmbedding w hw) := by
  exact (blockIsometry w hw).injective

/-- A Hilbert block embedding sends the standard unit vector to the corresponding block.
Blueprint support for `thm:block-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2BlockEmbedding_single_apply (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (n k : ℕ) :
    canonicalL2BlockEmbedding w hw (lp.single 2 n 1) k = w n k := by
  have h :=
    (show Orthonormal ℝ (blockL2 w hw) from by
    exact blocksOrthonormal w hw).orthogonalFamily.linearIsometry_apply_single
      (i := n) (1 : ℝ)
  have hv :
      blockIsometry w hw (lp.single 2 n 1) = blockL2 w hw n := by
    simpa only [blockIsometry, LinearIsometry.toSpanSingleton_apply, one_smul] using h
  exact congrArg (fun x : L2 ↦ x k) hv

private lemma canonicalBlockOperator_coordinates (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (z : CanonicalRealKaltonPeck) :
    canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockOperator w hw z) =
      blockTargetPair w (canonicalRealKaltonPeckPresentation.coordinates z) :=
  blockTargetVector_coordinates w hw z

/-- Canonical block operators intertwine the canonical inclusion and the Hilbert block isometry.
Blueprint support for `thm:block-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalBlockOperator_inclusion (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    (canonicalBlockOperator w hw).comp canonicalL2Inclusion =
      canonicalL2Inclusion.comp (canonicalL2BlockEmbedding w hw) := by
  apply ContinuousLinearMap.ext
  intro x
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    canonicalBlockOperator_coordinates, canonicalL2Inclusion_coordinates,
    canonicalL2Inclusion_coordinates]
  apply Prod.ext
  · change
      (rawBlockTransform w (fun n ↦ x n) + rawBlockCorrection w 0) =
      fun n ↦ canonicalL2BlockEmbedding w hw x n
    rw [rawBlockCorrection_zero, add_zero]
    rw [rawBlockTransform_eq_isometry w hw (fun n ↦ x n)
      (fromL2SquareSummable x)]
    rfl
  · exact rawBlockTransform_zero w

private lemma squareSummable_of_finite_support (x : ℕ → ℝ)
    (hx : Set.Finite {n | x n ≠ 0}) : IsSquareSummable x := by
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact hx.subset (by simp)

private lemma mul_summable_of_squareSummable (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    Summable (fun n ↦ x n * y n) := by
  change Summable (fun n ↦ inner ℝ (toL2 y hy n) (toL2 x hx n))
  exact lp.summable_inner _ _

private lemma rawBlockTransform_inner (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    (∑' k, rawBlockTransform w x k * rawBlockTransform w y k) =
      ∑' n, x n * y n := by
  have h := (blockIsometry w hw).inner_map_map (toL2 x hx) (toL2 y hy)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum] at h
  rw [← rawBlockTransform_eq_isometry w hw x hx,
    ← rawBlockTransform_eq_isometry w hw y hy] at h
  simpa only [RCLike.inner_apply, conj_trivial, toL2, mul_comm] using h

private lemma canonicalPairing_blockTargetPair_of_finite
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (p q : (ℕ → ℝ) × (ℕ → ℝ))
    (hp : IsFiniteCoordinatePair p) (hq : IsFiniteCoordinatePair q) :
    canonicalPairing (blockTargetPair w p) (blockTargetPair w q) =
      canonicalPairing p q := by
  have hp1 := squareSummable_of_finite_support p.1 hp.1
  have hp2 := squareSummable_of_finite_support p.2 hp.2
  have hq1 := squareSummable_of_finite_support q.1 hq.1
  have hq2 := squareSummable_of_finite_support q.2 hq.2
  have hBp1 := rawBlockTransform_squareSummable w hw p.1 hp1
  have hBp2 := rawBlockTransform_squareSummable w hw p.2 hp2
  have hBq1 := rawBlockTransform_squareSummable w hw q.1 hq1
  have hBq2 := rawBlockTransform_squareSummable w hw q.2 hq2
  have hsB1 := mul_summable_of_squareSummable _ _ hBp1 hBq2
  have hsB2 := mul_summable_of_squareSummable _ _ hBq1 hBp2
  have hs1 := mul_summable_of_squareSummable _ _ hp1 hq2
  have hs2 := mul_summable_of_squareSummable _ _ hq1 hp2
  rw [canonicalPairing, canonicalPairing]
  calc
    (∑' k, canonicalPairingTerm (blockTargetPair w p) (blockTargetPair w q) k) =
        ∑' k, (rawBlockTransform w p.1 k * rawBlockTransform w q.2 k -
          rawBlockTransform w q.1 k * rawBlockTransform w p.2 k) := by
      apply tsum_congr
      intro k
      by_cases hk : HasActiveBlock w k
      · simp [canonicalPairingTerm, blockTargetPair, rawBlockTransform,
          rawBlockCorrection, hk]
        ring
      · simp [canonicalPairingTerm, blockTargetPair, rawBlockTransform,
          rawBlockCorrection, hk]
    _ = (∑' k, rawBlockTransform w p.1 k * rawBlockTransform w q.2 k) -
        ∑' k, rawBlockTransform w q.1 k * rawBlockTransform w p.2 k :=
      hsB1.tsum_sub hsB2
    _ = (∑' n, p.1 n * q.2 n) - ∑' n, q.1 n * p.2 n := by
      rw [rawBlockTransform_inner w hw p.1 q.2 hp1 hq2,
        rawBlockTransform_inner w hw q.1 p.2 hq1 hp2]
    _ = ∑' n, (p.1 n * q.2 n - q.1 n * p.2 n) :=
      (hs1.tsum_sub hs2).symm
    _ = ∑' n, canonicalPairingTerm p q n := by
      apply tsum_congr
      intro n
      rfl

private lemma canonicalPairing_blockTargetPair_disjoint
    (w v : ℕ → ℕ → ℝ) (hdisjoint : AreMutuallySupportDisjoint w v)
    (p q : (ℕ → ℝ) × (ℕ → ℝ)) :
    canonicalPairing (blockTargetPair w p) (blockTargetPair v q) = 0 := by
  rw [canonicalPairing]
  have hzero :
      canonicalPairingTerm (blockTargetPair w p) (blockTargetPair v q) = 0 := by
    funext k
    by_cases hwk : HasActiveBlock w k
    · have hvk : ¬HasActiveBlock v k := by
        rintro ⟨m, hvm⟩
        obtain ⟨n, hwn⟩ := hwk
        exact Set.disjoint_left.1 (hdisjoint n m) hwn hvm
      simp [canonicalPairingTerm, blockTargetPair, rawBlockTransform, rawBlockCorrection, hvk]
    · simp [canonicalPairingTerm, blockTargetPair, rawBlockTransform, rawBlockCorrection, hwk]
  rw [hzero]
  exact tsum_zero

private lemma canonicalBlockOperator_preserves_form
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (z z' : CanonicalRealKaltonPeck) :
    canonicalKaltonSwansonForm.toDual (canonicalBlockOperator w hw z)
        (canonicalBlockOperator w hw z') =
      canonicalKaltonSwansonForm.toDual z z' := by
  let D : Set CanonicalRealKaltonPeck :=
    {x | IsFiniteCoordinatePair (canonicalRealKaltonPeckPresentation.coordinates x)}
  have hD : Dense D := canonicalKaltonPeckBanach.2.2.2
  have hfinite : ∀ x ∈ D, ∀ y ∈ D,
      canonicalKaltonSwansonForm.toDual (canonicalBlockOperator w hw x)
          (canonicalBlockOperator w hw y) =
        canonicalKaltonSwansonForm.toDual x y := by
    intro x hx y hy
    change canonicalPairing
        (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockOperator w hw x))
        (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockOperator w hw y)) =
      canonicalPairing (canonicalRealKaltonPeckPresentation.coordinates x)
        (canonicalRealKaltonPeckPresentation.coordinates y)
    rw [canonicalBlockOperator_coordinates w hw x,
      canonicalBlockOperator_coordinates w hw y]
    exact canonicalPairing_blockTargetPair_of_finite w hw _ _ hx hy
  apply eqOn_closure₂' hfinite
  · intro x
    exact (canonicalKaltonSwansonForm.toDual
      (canonicalBlockOperator w hw x)).continuous.comp
        (canonicalBlockOperator w hw).continuous
  · intro y
    exact Continuous.clm_apply
      (canonicalKaltonSwansonForm.toDual.continuous.comp
        (canonicalBlockOperator w hw).continuous)
      continuous_const
  · intro x
    exact (canonicalKaltonSwansonForm.toDual x).continuous
  · intro y
    exact Continuous.clm_apply canonicalKaltonSwansonForm.toDual.continuous continuous_const
  · exact hD z
  · exact hD z'

private lemma canonicalBlockOperators_cross_form
    (w v : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w)
    (hv : IsSuccessiveNormalizedBlockSequence v)
    (hdisjoint : AreMutuallySupportDisjoint w v)
    (z z' : CanonicalRealKaltonPeck) :
    canonicalKaltonSwansonForm.toDual (canonicalBlockOperator w hw z)
      (canonicalBlockOperator v hv z') = 0 := by
  change canonicalPairing
      (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockOperator w hw z))
      (canonicalRealKaltonPeckPresentation.coordinates (canonicalBlockOperator v hv z')) = 0
  rw [canonicalBlockOperator_coordinates w hw z,
    canonicalBlockOperator_coordinates v hv z']
  exact canonicalPairing_blockTargetPair_disjoint w v hdisjoint _ _

/-- The complete canonical normalized-block interface, including both cross-family identities.
Blueprint label: `thm:block-primary`; audit IDs `EXT-K-BLOCK`,
`RES-BLOCK-OPERATOR-IDENTITIES`, and `HID-EVEN-ODD-BLOCK-RELATIONS`. -/
theorem canonicalNormalizedBlock (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    let W := canonicalBlockOperator w hw
    (∀ n, canonicalRealKaltonPeckPresentation.coordinates (W (canonicalFirstBasisVector n)) =
        (w n, 0)) ∧
      (∀ n, canonicalRealKaltonPeckPresentation.coordinates (W (canonicalSecondBasisVector n)) =
        (centralizer (w n), w n)) ∧
      Function.Injective W ∧
      Submodule.ClosedComplemented W.range ∧
      (∀ z z', canonicalKaltonSwansonForm.toDual (W z) (W z') =
        canonicalKaltonSwansonForm.toDual z z') ∧
      canonicalKaltonSwansonForm.adjoint W * W = 1 ∧
      let P := W * canonicalKaltonSwansonForm.adjoint W
      P ^ 2 = P ∧ P.range = W.range ∧
        ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
          AreMutuallySupportDisjoint w v →
            canonicalKaltonSwansonForm.adjoint W * canonicalBlockOperator v hv = 0 ∧
              canonicalKaltonSwansonForm.adjoint (canonicalBlockOperator v hv) * W = 0 := by
  let W := canonicalBlockOperator w hw
  change
    (∀ n, canonicalRealKaltonPeckPresentation.coordinates
        (W (canonicalFirstBasisVector n)) = (w n, 0)) ∧
      (∀ n, canonicalRealKaltonPeckPresentation.coordinates
        (W (canonicalSecondBasisVector n)) = (centralizer (w n), w n)) ∧
      Function.Injective W ∧
      Submodule.ClosedComplemented W.range ∧
      (∀ z z', canonicalKaltonSwansonForm.toDual (W z) (W z') =
        canonicalKaltonSwansonForm.toDual z z') ∧
      canonicalKaltonSwansonForm.adjoint W * W = 1 ∧
      let P := W * canonicalKaltonSwansonForm.adjoint W
      P ^ 2 = P ∧ P.range = W.range ∧
        ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
          AreMutuallySupportDisjoint w v →
            canonicalKaltonSwansonForm.adjoint W * canonicalBlockOperator v hv = 0 ∧
              canonicalKaltonSwansonForm.adjoint (canonicalBlockOperator v hv) * W = 0
  have hfirst (n : ℕ) :
      canonicalRealKaltonPeckPresentation.coordinates
          (W (canonicalFirstBasisVector n)) = (w n, 0) := by
    rw [show W = canonicalBlockOperator w hw by rfl,
      canonicalBlockOperator_coordinates, (canonicalBasisCoordinates n).1]
    change
      (rawBlockTransform w (standardBasisSequence n) + rawBlockCorrection w 0,
        rawBlockTransform w 0) = (w n, 0)
    rw [rawBlockTransform_standardBasis w hw n, rawBlockCorrection_zero,
      rawBlockTransform_zero]
    simp
  have hsecond (n : ℕ) :
      canonicalRealKaltonPeckPresentation.coordinates
          (W (canonicalSecondBasisVector n)) = (centralizer (w n), w n) := by
    rw [show W = canonicalBlockOperator w hw by rfl,
      canonicalBlockOperator_coordinates, (canonicalBasisCoordinates n).2]
    change
      (rawBlockTransform w 0 + rawBlockCorrection w (standardBasisSequence n),
        rawBlockTransform w (standardBasisSequence n)) =
          (centralizer (w n), w n)
    rw [rawBlockTransform_zero, rawBlockCorrection_standardBasis w hw n,
      rawBlockTransform_standardBasis w hw n]
    simp
  have hpreserves (z z' : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual (W z) (W z') =
        canonicalKaltonSwansonForm.toDual z z' := by
    simpa [W] using canonicalBlockOperator_preserves_form w hw z z'
  have hadjoint : canonicalKaltonSwansonForm.adjoint W * W = 1 := by
    apply ContinuousLinearMap.ext
    intro z
    apply canonicalKaltonSwansonForm.toDual.injective
    apply ContinuousLinearMap.ext
    intro z'
    change canonicalKaltonSwansonForm.toDual
      (canonicalKaltonSwansonForm.adjoint W (W z)) z' =
        canonicalKaltonSwansonForm.toDual z z'
    rw [Forms.adjoint_apply]
    exact hpreserves z z'
  have hleft : Function.LeftInverse (canonicalKaltonSwansonForm.adjoint W) W := by
    intro z
    change (canonicalKaltonSwansonForm.adjoint W * W) z = z
    rw [hadjoint]
    rfl
  have hclosed : Submodule.ClosedComplemented W.range :=
    W.closedComplemented_range_of_leftInverse
      (canonicalKaltonSwansonForm.adjoint W) hleft
  have hprojection :
      (W * canonicalKaltonSwansonForm.adjoint W) ^ 2 =
        W * canonicalKaltonSwansonForm.adjoint W := by
    simp only [pow_two]
    rw [mul_assoc, ← mul_assoc (canonicalKaltonSwansonForm.adjoint W), hadjoint]
    simp
  have hprojectionRange :
      (W * canonicalKaltonSwansonForm.adjoint W).range = W.range := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      exact ⟨canonicalKaltonSwansonForm.adjoint W x, rfl⟩
    · rintro z ⟨x, rfl⟩
      refine ⟨W x, ?_⟩
      change W (canonicalKaltonSwansonForm.adjoint W (W x)) = W x
      rw [hleft x]
  have hskew (x y : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual x y =
        -canonicalKaltonSwansonForm.toDual y x := by
    have h := canonicalKaltonSwansonForm.alternating (x + y)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  have hcross :
      ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
        AreMutuallySupportDisjoint w v →
          canonicalKaltonSwansonForm.adjoint W * canonicalBlockOperator v hv = 0 ∧
            canonicalKaltonSwansonForm.adjoint (canonicalBlockOperator v hv) * W = 0 := by
    intro v hv hdisjoint
    let V := canonicalBlockOperator v hv
    have hcrossForm (x y : CanonicalRealKaltonPeck) :
        canonicalKaltonSwansonForm.toDual (W x) (V y) = 0 := by
      simpa [W, V] using
        canonicalBlockOperators_cross_form w v hw hv hdisjoint x y
    constructor
    · change (canonicalKaltonSwansonForm.adjoint W).comp V = 0
      apply ContinuousLinearMap.ext
      intro x
      apply canonicalKaltonSwansonForm.toDual.injective
      apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
      rw [Forms.adjoint_apply, hskew, hcrossForm]
      exact neg_zero
    · change (canonicalKaltonSwansonForm.adjoint V).comp W = 0
      apply ContinuousLinearMap.ext
      intro x
      apply canonicalKaltonSwansonForm.toDual.injective
      apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
      rw [Forms.adjoint_apply]
      exact hcrossForm x y
  refine ⟨hfirst, hsecond, hleft.injective, hclosed, hpreserves, hadjoint, ?_⟩
  exact ⟨hprojection, hprojectionRange, hcross⟩

/-- The block operator conjugated to an arbitrary complete presented model.
Blueprint label: `thm:block-transport`; audit ID `RES-BLOCK-OPERATOR-IDENTITIES`. -/
def transportedBlockOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) : X →L[ℝ] X := by
  let e := presentationEquiv hX canonicalRealKaltonPeckPresentation
  exact e.symm.toContinuousLinearMap.comp
    ((canonicalBlockOperator w hw).comp e.toContinuousLinearMap)

/-- The complete normalized-block interface transported through presentation equivalence.
Blueprint label: `thm:block-transport`; audit IDs `INF-KP-COORDINATE-EQUIVALENCE`,
`EXT-KS-STRONG`, `EXT-K-BLOCK`, and `HID-EVEN-ODD-BLOCK-RELATIONS`. -/
theorem transportedNormalizedBlock {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) :
    let e := presentationEquiv hX canonicalRealKaltonPeckPresentation
    let W := transportedBlockOperator hX w hw
    let Wc := canonicalBlockOperator w hw
    (∀ x, e (W x) = Wc (e x)) ∧
      Function.Injective W ∧
      Submodule.ClosedComplemented W.range ∧
      (∀ x y, (transportedKaltonSwansonForm hX).toDual (W x) (W y) =
        (transportedKaltonSwansonForm hX).toDual x y) ∧
      (transportedKaltonSwansonForm hX).adjoint W * W = 1 ∧
      let P := W * (transportedKaltonSwansonForm hX).adjoint W
      P ^ 2 = P ∧ P.range = W.range ∧
        ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
          AreMutuallySupportDisjoint w v →
            (transportedKaltonSwansonForm hX).adjoint W *
                transportedBlockOperator hX v hv = 0 ∧
              (transportedKaltonSwansonForm hX).adjoint
                  (transportedBlockOperator hX v hv) * W = 0 := by
  let e := presentationEquiv hX canonicalRealKaltonPeckPresentation
  let W := transportedBlockOperator hX w hw
  let Wc := canonicalBlockOperator w hw
  change
    (∀ x, e (W x) = Wc (e x)) ∧
      Function.Injective W ∧
      Submodule.ClosedComplemented W.range ∧
      (∀ x y, (transportedKaltonSwansonForm hX).toDual (W x) (W y) =
        (transportedKaltonSwansonForm hX).toDual x y) ∧
      (transportedKaltonSwansonForm hX).adjoint W * W = 1 ∧
      let P := W * (transportedKaltonSwansonForm hX).adjoint W
      P ^ 2 = P ∧ P.range = W.range ∧
        ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
          AreMutuallySupportDisjoint w v →
            (transportedKaltonSwansonForm hX).adjoint W *
                transportedBlockOperator hX v hv = 0 ∧
              (transportedKaltonSwansonForm hX).adjoint
                  (transportedBlockOperator hX v hv) * W = 0
  have hintertwine (x : X) : e (W x) = Wc (e x) := by
    change e (e.symm (Wc (e x))) = Wc (e x)
    exact e.apply_symm_apply _
  have hcan := canonicalNormalizedBlock w hw
  dsimp only at hcan
  have hcanPreserves := hcan.2.2.2.2.1
  have hpreserves (x y : X) :
      (transportedKaltonSwansonForm hX).toDual (W x) (W y) =
        (transportedKaltonSwansonForm hX).toDual x y := by
    rw [transportedKaltonSwansonForm_apply, transportedKaltonSwansonForm_apply]
    rw [hintertwine x, hintertwine y]
    exact hcanPreserves (e x) (e y)
  have hadjoint : (transportedKaltonSwansonForm hX).adjoint W * W = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply (transportedKaltonSwansonForm hX).toDual.injective
    apply ContinuousLinearMap.ext
    intro y
    change (transportedKaltonSwansonForm hX).toDual
      ((transportedKaltonSwansonForm hX).adjoint W (W x)) y =
        (transportedKaltonSwansonForm hX).toDual x y
    rw [Forms.adjoint_apply]
    exact hpreserves x y
  have hleft :
      Function.LeftInverse ((transportedKaltonSwansonForm hX).adjoint W) W := by
    intro x
    change ((transportedKaltonSwansonForm hX).adjoint W * W) x = x
    rw [hadjoint]
    rfl
  have hclosed : Submodule.ClosedComplemented W.range :=
    W.closedComplemented_range_of_leftInverse
      ((transportedKaltonSwansonForm hX).adjoint W) hleft
  have hprojection :
      (W * (transportedKaltonSwansonForm hX).adjoint W) ^ 2 =
        W * (transportedKaltonSwansonForm hX).adjoint W := by
    simp only [pow_two]
    rw [mul_assoc,
      ← mul_assoc ((transportedKaltonSwansonForm hX).adjoint W), hadjoint]
    simp
  have hprojectionRange :
      (W * (transportedKaltonSwansonForm hX).adjoint W).range = W.range := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      exact ⟨(transportedKaltonSwansonForm hX).adjoint W x, rfl⟩
    · rintro z ⟨x, rfl⟩
      refine ⟨W x, ?_⟩
      change W ((transportedKaltonSwansonForm hX).adjoint W (W x)) = W x
      rw [hleft x]
  have hskew (x y : X) :
      (transportedKaltonSwansonForm hX).toDual x y =
        -(transportedKaltonSwansonForm hX).toDual y x := by
    have h := (transportedKaltonSwansonForm hX).alternating (x + y)
    simp only [map_add, add_apply, (transportedKaltonSwansonForm hX).alternating,
      add_zero, zero_add] at h
    linarith
  have hcanCross := hcan.2.2.2.2.2.2.2.2
  have hcross :
      ∀ v (hv : IsSuccessiveNormalizedBlockSequence v),
        AreMutuallySupportDisjoint w v →
          (transportedKaltonSwansonForm hX).adjoint W *
              transportedBlockOperator hX v hv = 0 ∧
            (transportedKaltonSwansonForm hX).adjoint
                (transportedBlockOperator hX v hv) * W = 0 := by
    intro v hv hdisjoint
    let V := transportedBlockOperator hX v hv
    let Vc := canonicalBlockOperator v hv
    have hintertwineV (x : X) : e (V x) = Vc (e x) := by
      change e (e.symm (Vc (e x))) = Vc (e x)
      exact e.apply_symm_apply _
    have hcanonicalCross :
        canonicalKaltonSwansonForm.adjoint Vc * Wc = 0 := by
      simpa [Wc, Vc] using (hcanCross v hv hdisjoint).2
    have hcrossForm (x y : X) :
        (transportedKaltonSwansonForm hX).toDual (W x) (V y) = 0 := by
      rw [transportedKaltonSwansonForm_apply, hintertwine x, hintertwineV y]
      rw [← Forms.adjoint_apply]
      have hz : canonicalKaltonSwansonForm.adjoint Vc (Wc (e x)) = 0 := by
        change (canonicalKaltonSwansonForm.adjoint Vc * Wc) (e x) = 0
        rw [hcanonicalCross]
        rfl
      rw [hz]
      simp
    constructor
    · change ((transportedKaltonSwansonForm hX).adjoint W).comp V = 0
      apply ContinuousLinearMap.ext
      intro x
      apply (transportedKaltonSwansonForm hX).toDual.injective
      apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
      rw [Forms.adjoint_apply, hskew, hcrossForm]
      exact neg_zero
    · change ((transportedKaltonSwansonForm hX).adjoint V).comp W = 0
      apply ContinuousLinearMap.ext
      intro x
      apply (transportedKaltonSwansonForm hX).toDual.injective
      apply ContinuousLinearMap.ext
      intro y
      simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero]
      rw [Forms.adjoint_apply]
      exact hcrossForm x y
  refine ⟨hintertwine, hleft.injective, hclosed, hpreserves, hadjoint, ?_⟩
  exact ⟨hprojection, hprojectionRange, hcross⟩

end


end KaltonPeck.Support.Symplectic

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
