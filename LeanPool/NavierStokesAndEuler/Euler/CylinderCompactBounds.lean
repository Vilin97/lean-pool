/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCompactTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

@[expose] public section

/-!
True mixed L² derivative bounds for compact smooth cylinder data. One
fixed compact support set supplies the L² mass factor at every order.
The conversion to fixed-Hq word sums is performed once on the initial
datum, before any same-radius inverse estimate is applied.
-/

noncomputable section

namespace EulerCylinderCompact

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMetricTransport EulerLiftedWeakDerivative
  EulerLpDerivative EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

universe u

variable (P : ℝ) [Fact (0 < P)]

def supportMass (K : Set (LiftDomain P)) (hK : IsCompact K) : ℝ :=
  ‖(indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1 : ℝ) :
    Lp ℝ 2 (liftMeasure P))‖

namespace CompactField

variable {P} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] in
theorem derivative_support (A : CompactField P V) : tsupport A.derivative.field ⊆ tsupport A.field
  := by
  apply closure_minimal _ (isClosed_tsupport A.field)
  intro x hx
  by_contra hn
  exact hx (fieldFDeriv_zero_outside P A.field x hn)

theorem toLp_norm_le (A : CompactField P V) (K : Set (LiftDomain P)) (hK : IsCompact K)
    (hs : tsupport A.field ⊆ K) (C : ℝ) (hb : ∀ x, ‖A.field x‖ ≤ C) :
    ‖A.toLp‖ ≤ C*supportMass P K hK := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [A.toLp_ae,
    (indicatorConstLp_coeFn (p := 2) (μ := liftMeasure P)
      (hs := hK.isClosed.measurableSet) (hμs := hK.measure_ne_top) (c := (1 : ℝ)))] with x ha hk
  rw [ha,hk]
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx,norm_one,mul_one] using hb x
  · have hz : A.field x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp only [Set.indicator_of_notMem hx,hz,norm_zero,mul_zero,le_refl]

private theorem norm_iteratedFDeriv_translation_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : CompactField P V)
      (K : Set (LiftDomain P)) (hK : IsCompact K) (_hs : tsupport A.field ⊆ K)
      (C : ℝ) (_hb : ∀ x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C)
      (a : LiftTangent),
      ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate P b A.toLp) a‖ ≤ C*supportMass P K hK
        := by
  induction n with
  | zero =>
    intro V _ _ A K hK hs C hb a
    rw [norm_iteratedFDeriv_zero,LinearIsometry.norm_map]
    apply A.toLp_norm_le K hK hs C
    intro x
    simpa only [norm_iteratedFDeriv_zero,localFieldLift,Prod.fst_zero,Prod.snd_zero,
      AddCircle.coe_zero,add_zero] using hb x
  | succ n ih =>
    intro V _ _ A K hK hs C hb a
    rw [← norm_iteratedFDeriv_fderiv,A.translation_fderiv]
    have hl := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
      (F := CylinderL2 P (LiftTangent →L[ℝ] V)) (G := LiftTangent →L[ℝ] CylinderL2 P V)
      (derivativeBundling (liftMeasure P))
      (A.derivative.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
    have hi := ih (LiftTangent →L[ℝ] V) A.derivative K hK
      (A.derivative_support.trans hs) C (fun x => by
        change ‖iteratedFDeriv ℝ n (localFieldLift P (fieldFDeriv P A.field) x) 0‖ ≤ C
        rw [localFieldLift_fieldFDeriv,norm_iteratedFDeriv_fderiv]
        exact hb x) a
    exact hl.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := LiftTangent) (V := V) (liftMeasure P)) (norm_nonneg
        _)).trans
        (by simpa only [one_mul] using hi))

theorem norm_iteratedFDeriv_translation_le (A : CompactField P V)
    (K : Set (LiftDomain P)) (hK : IsCompact K) (hs : tsupport A.field ⊆ K)
    (n : ℕ) (C : ℝ) (hb : ∀ x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C)
    (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate P b A.toLp) a‖ ≤ C*supportMass P K hK :=
  norm_iteratedFDeriv_translation_aux n V A K hK hs C hb a

theorem translation_gevrey (A : CompactField P V)
    (K : Set (LiftDomain P)) (hK : IsCompact K) (hs : tsupport A.field ⊆ K)
    (R C : ℝ) (hb : ∀ n x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C*majorant R 0 n)
    (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate P b A.toLp) a‖ ≤
      (C*supportMass P K hK)*majorant R 0 n :=
  (A.norm_iteratedFDeriv_translation_le K hK hs n (C*majorant R 0 n) (hb n) a).trans_eq (by ring)

theorem translation_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (A : CompactField P V) (K : Set (LiftDomain P)) (hK : IsCompact K) (hs : tsupport A.field ⊆ K)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C*majorant R 0 n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => translate P b A.toLp) n a ≤
      sobolevCoefficientAmplitude ι q R (C*supportMass P K hK)*
        majorant (sobolevCoefficientRadius ι R) 0 n := by
  have hm : 0 ≤ supportMass P K hK := norm_nonneg _
  have hi := coefficientBlock_of_tensor_bound directions hd q
    (fun b : LiftTangent => translate P b A.toLp) A.translation_contDiff
    R (C*supportMass P K hK) hR (mul_nonneg hC hm) (A.translation_gevrey K hK hs R C hb) n a
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
  have hl : block directions q (fun b : LiftTangent => translate P b A.toLp) n a ≤
      coefficientBlock directions q (fun b : LiftTangent => translate P b A.toLp) n a := by
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hpow (block_nonneg directions q _ n
      a))
  exact hl.trans hi

end CompactField
end EulerCylinderCompact
