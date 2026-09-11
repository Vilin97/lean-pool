/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalDatum
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GevreyFunctions
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCompactTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

/-!
Actual mixed L² and fixed-Hq bounds for χ₁(y) fδ(θ) ξT.  All constants
are explicit: the only support factor is the fixed L² mass of the cutoff
support cylinder.  The one-time conversion from tensor jets to words
precedes the fixed-radius linear solves.
-/

section

/-!
True mixed L² derivative bounds for compact smooth cylinder data. One
fixed compact support set supplies the L² mass factor at every order.
The conversion to fixed-Hq word sums is performed once on the initial
datum, before any same-radius inverse estimate is applied.
-/

@[expose] public section

noncomputable section

namespace EulerCylinderCompact

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMetricTransport EulerLiftedWeakDerivative
  EulerLpDerivative EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

universe u

variable (P : ℝ) [Fact (0 < P)]

/-- Support mass, given by `‖(indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1
: ℝ) : Lp ℝ 2 (liftMeasure P))‖`. -/
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
    (R C : ℝ) (hb : ∀ n x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C * majorant R 0 n)
    (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate P b A.toLp) a‖ ≤
      (C*supportMass P K hK)*majorant R 0 n :=
  (A.norm_iteratedFDeriv_translation_le K hK hs n (C*majorant R 0 n) (hb n) a).trans_eq (by ring)

theorem translation_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (A : CompactField P V) (K : Set (LiftDomain P)) (hK : IsCompact K) (hs : tsupport A.field ⊆ K)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (localFieldLift P A.field x) 0‖ ≤ C * majorant R 0 n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => translate P b A.toLp) n a ≤
      sobolevCoefficientAmplitude ι q R (C*supportMass P K hK) *
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerSpatialCutoffs EulerPeriodicProfile EulerGevreyCutoff
  EulerCylinderCompact EulerLpCylinderTranslation EulerGevrey EulerGevreyFunctions
  EulerParameterWordGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

/-- Jet radius, given by `64 + 40 * (δ^2)⁻¹`. -/
def jetRadius (δ : ℝ) : ℝ := 64 + 40 * (δ^2)⁻¹

/-- Scalar jet cost, given by `3 * (9 / rawBump 0)^3 * (100 * (δ^2)⁻¹)`. -/
def scalarJetCost (δ : ℝ) : ℝ := 3 * (9 / rawBump 0)^3 * (100 * (δ^2)⁻¹)

theorem jetRadius_nonneg (δ : ℝ) : 0 ≤ jetRadius δ := by
  unfold jetRadius
  positivity

theorem scalarJetCost_nonneg (δ : ℝ) : 0 ≤ scalarJetCost δ := by
  have := rawBump_pos_zero
  unfold scalarJetCost
  positivity

private theorem cutoffLift_bound (y : Space) (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => innerCutoff (y+b.1)) a‖ ≤
      (9 / rawBump 0)^3 * majorant 64 0 n := by
  let L : LiftTangent →L[ℝ] Space := ContinuousLinearMap.fst ℝ Space ℝ
  have hf : ContDiff ℝ ∞ (fun z : Space => innerCutoff (y+z)) :=
    innerCutoff_contDiff.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n ((fun z : Space => innerCutoff (y+z)) ∘ L) a‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf a (by simp)]
  rw [iteratedFDeriv_comp_add_left]
  have hn := (iteratedFDeriv ℝ n (fun z : Space => innerCutoff (y+z)) (L
      a)).norm_compContinuousLinearMap_le
    (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,iteratedFDeriv_comp_add_left] at hn
  have hp : ‖L‖^n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) (norm_fst_le ℝ Space ℝ) n
  exact hn.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans
    (by simpa only [mul_one] using innerCutoff_gevrey n (y+L a)))

theorem scalarField_jet_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (x : LiftDomain period) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (localFieldLift period (scalarField δ) x) a‖ ≤
      scalarJetCost δ * majorant (jetRadius δ) 0 n := by
  rcases x with ⟨y,θ⟩
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective θ
  rw [← hs,local_scalarField]
  have hc : 0 ≤ (9 / rawBump 0)^3 := by have := rawBump_pos_zero; positivity
  have hp : 0 ≤ 100*(δ^2)⁻¹ := by positivity
  have hR₁ : (64 : ℝ) ≤ jetRadius δ := le_add_of_nonneg_right (by positivity)
  have hR₂ : 40*(δ^2)⁻¹ ≤ jetRadius δ := by unfold jetRadius; linarith
  have hb₁ (k : ℕ) (b : LiftTangent) :=
    (cutoffLift_bound y k b).trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono 64 (jetRadius δ) (by norm_num) hR₁ 0 k) hc)
  have hb₂ (k : ℕ) (b : LiftTangent) :
      ‖iteratedFDeriv ℝ k (fun z : LiftTangent => profile δ (s+z.2)) b‖ ≤
        (100*(δ^2)⁻¹) * majorant (jetRadius δ) 0 k := by
    have hh := affine_composition_bound (profile δ) (profile_contDiff δ hδ)
      (ContinuousLinearMap.snd ℝ Space ℝ) s (40*(δ^2)⁻¹) (100*(δ^2)⁻¹) 1
      (by positivity) hp (by norm_num) (norm_snd_le ℝ Space ℝ)
      (profile_gevrey δ hδ hδ1) k b
    simp only [mul_one,add_comm _ s] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono _ (jetRadius δ) (by positivity) hR₂ 0 k) hp)
  exact product_bound _ _
    (innerCutoff_contDiff.comp (contDiff_const.add contDiff_fst))
    ((profile_contDiff δ hδ).comp (contDiff_const.add contDiff_snd))
    (jetRadius δ) ((9/rawBump 0)^3) (100*(δ^2)⁻¹)
    (jetRadius_nonneg δ) hc hp hb₁ hb₂ n a

theorem field_jet_bound {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
    (n : ℕ) (x : LiftDomain period) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (localFieldLift period (field δ ξ) x) a‖ ≤
      (scalarJetCost δ * ‖ξ‖) * majorant (jetRadius δ) 0 n := by
  let L : ℝ →L[ℝ] U := toSpanSingleton ℝ ξ
  have hn := L.norm_iteratedFDeriv_comp_left
    ((scalarField_smooth δ hδ x).contDiffAt (x := a)) (n := n) (by simp)
  change ‖iteratedFDeriv ℝ n (L ∘ localFieldLift period (scalarField δ) x) a‖ ≤ _
  exact hn.trans ((mul_le_mul_of_nonneg_left (scalarField_jet_bound δ hδ hδ1 n x a)
    (norm_nonneg L)).trans_eq (by simp only [L,norm_toSpanSingleton]; ring))

/-- Terminal mass, given by `supportMass period supportSet supportSet_compact`. -/
def terminalMass : ℝ := supportMass period supportSet supportSet_compact

theorem terminalMass_nonneg : 0 ≤ terminalMass := norm_nonneg _

theorem terminal_jet_bound {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U) (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => translate period b (terminal δ hδ ξ)) a‖ ≤
      (scalarJetCost δ * ‖ξ‖ * terminalMass) * majorant (jetRadius δ) 0 n :=
  (compactField δ hδ ξ).translation_gevrey supportSet supportSet_compact (field_support δ ξ)
    (jetRadius δ) (scalarJetCost δ * ‖ξ‖) (fun k x => field_jet_bound δ hδ hδ1 ξ k x 0) n a

/-- Word radius, given by `sobolevCoefficientRadius ι (jetRadius δ)`. -/
def wordRadius (ι : Type*) [Fintype ι] (δ : ℝ) : ℝ :=
  sobolevCoefficientRadius ι (jetRadius δ)

/-- Word cost, given by `sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ *
terminalMass)`. -/
def wordCost (ι : Type*) [Fintype ι] (q : ℕ) (δ : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * terminalMass)

theorem terminal_block_bound {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => translate period b (terminal δ hδ ξ)) n a ≤
      sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * ‖ξ‖ * terminalMass) *
        majorant (wordRadius ι δ) 0 n :=
  (compactField δ hδ ξ).translation_block_bound directions hd q supportSet supportSet_compact
    (field_support δ ξ) (jetRadius δ) (scalarJetCost δ * ‖ξ‖)
    (jetRadius_nonneg δ) (mul_nonneg (scalarJetCost_nonneg δ) (norm_nonneg ξ))
    (fun k x => field_jet_bound δ hδ hδ1 ξ k x 0) n a

end EulerPacketTerminalDatum
