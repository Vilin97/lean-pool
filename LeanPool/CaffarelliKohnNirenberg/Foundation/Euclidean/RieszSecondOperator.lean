/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecond
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondBadPart
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Global
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Riesz Second Operator

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

abbrev rieszSecondL2 := Lp ℝ 2 (volume : Measure Vec3)

def rieszSecondSchwartzEmbedding :
    SchwartzMap Vec3 ℝ →L[ℝ] rieszSecondL2 :=
  SchwartzMap.toLpCLM ℝ ℝ 2 volume

/- The smooth input map is kept as a bounded map into the completed `L²`
   space.  Its norm bound is the global endpoint estimate. -/
structure RieszSecondL2Input (i j : Fin 3) where
  smoothMap : SchwartzMap Vec3 ℝ →L[ℝ] rieszSecondL2
  smooth_bound : ∀ φ, ‖smoothMap φ‖ ≤ ‖rieszSecondSchwartzEmbedding φ‖
  smooth_hessian : ∀ (F : Vec3 → ℝ)
    (_hF : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F),
    ∃ hmem : MemLp (mixedSecond (pressureNewtonianPotential F) i j)
        (2 : ℝ≥0∞) volume,
      smoothMap (_hFc.toSchwartzMap _hF) = MemLp.toLp _ hmem

/- The completion extension is made with the norm-controlled extension API;
   no choice of an approximating sequence is retained in the definition. -/
def rieszSecondL2Extension {i j : Fin 3} (hL2 : RieszSecondL2Input i j) :
    rieszSecondL2 →L[ℝ] rieszSecondL2 :=
  LinearMap.mkContinuous
    (hL2.smoothMap.toLinearMap.extendOfNorm
      rieszSecondSchwartzEmbedding.toLinearMap)
    1 (by
      intro f
      exact LinearMap.norm_extendOfNorm_apply_le
        (SchwartzMap.denseRange_toLpCLM (p := (2 : ℝ≥0∞)) (by norm_num))
        1 (fun φ => by
          change ‖hL2.smoothMap φ‖ ≤ 1 *
            ‖rieszSecondSchwartzEmbedding φ‖
          simpa only [one_mul] using hL2.smooth_bound φ) f)

theorem rieszSecondL2Extension_agrees {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (φ : SchwartzMap Vec3 ℝ) :
    rieszSecondL2Extension hL2 (rieszSecondSchwartzEmbedding φ) =
      hL2.smoothMap φ := by
  exact LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toLpCLM (p := (2 : ℝ≥0∞))
      (by norm_num))
    (by
      refine ⟨1, ?_⟩
      intro ψ
      change ‖hL2.smoothMap ψ‖ ≤ 1 *
        ‖rieszSecondSchwartzEmbedding ψ‖
      simpa only [one_mul] using hL2.smooth_bound ψ) φ

theorem rieszSecondL2Extension_smooth_hessian {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    ∃ hmem : MemLp (mixedSecond (pressureNewtonianPotential F) i j)
        (2 : ℝ≥0∞) volume,
      rieszSecondL2Extension hL2 (MemLp.toLp F
        (hF.continuous.memLp_of_hasCompactSupport hFc)) =
        MemLp.toLp (mixedSecond (pressureNewtonianPotential F) i j) hmem := by
  obtain ⟨hmem, hEq⟩ := hL2.smooth_hessian F hF hFc
  refine ⟨hmem, ?_⟩
  calc
    rieszSecondL2Extension hL2 (MemLp.toLp F
        (hF.continuous.memLp_of_hasCompactSupport hFc)) =
        hL2.smoothMap (hFc.toSchwartzMap hF) := by
      rw [show MemLp.toLp F
          (hF.continuous.memLp_of_hasCompactSupport hFc) =
          rieszSecondSchwartzEmbedding (hFc.toSchwartzMap hF) by
            apply MemLp.toLp_congr
            · exact hF.continuous.memLp_of_hasCompactSupport hFc
            · exact Filter.Eventually.of_forall (fun _ => rfl)]
      exact rieszSecondL2Extension_agrees hL2 (hFc.toSchwartzMap hF)
    _ = MemLp.toLp (mixedSecond (pressureNewtonianPotential F) i j) hmem := hEq

theorem rieszSecondL2Extension_norm_le {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (f : rieszSecondL2) :
    ‖rieszSecondL2Extension hL2 f‖ ≤ ‖f‖ := by
  have hDense : DenseRange rieszSecondSchwartzEmbedding := by
    simpa only [rieszSecondSchwartzEmbedding] using
      (SchwartzMap.denseRange_toLpCLM (p := (2 : ℝ≥0∞)) (by norm_num))
  change ‖(hL2.smoothMap.toLinearMap.extendOfNorm
      rieszSecondSchwartzEmbedding.toLinearMap) f‖ ≤ ‖f‖
  simpa only [one_mul] using
    (LinearMap.norm_extendOfNorm_apply_le
    hDense 1
    (fun φ => by
      change ‖hL2.smoothMap φ‖ ≤ 1 *
        ‖rieszSecondSchwartzEmbedding φ‖
      simpa only [one_mul] using hL2.smooth_bound φ) f)

def rieszSecondLpMeasurableRepresentative (u : rieszSecondL2) : Vec3 → ℝ :=
  (Lp.aestronglyMeasurable u).aemeasurable.mk u

theorem rieszSecondLpMeasurableRepresentative_measurable
    (u : rieszSecondL2) :
  Measurable (rieszSecondLpMeasurableRepresentative u) := by
  exact (Lp.aestronglyMeasurable u).aemeasurable.measurable_mk

theorem rieszSecondLpMeasurableRepresentative_ae_eq
    (u : rieszSecondL2) :
  (u : Vec3 → ℝ) =ᵐ[volume]
      rieszSecondLpMeasurableRepresentative u := by
  exact (Lp.aestronglyMeasurable u).aemeasurable.ae_eq_mk

/- The endpoint map is defined on the completed `L²` class.  No value is
   assigned to a raw function outside `L²`; doing so by zero would destroy
   sublinearity on the sum of the endpoint classes. -/
def rieszSecondL2MeasurableOperator {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) : Vec3 → ℝ :=
  rieszSecondLpMeasurableRepresentative (rieszSecondL2Extension hL2 u)

theorem rieszSecondL2MeasurableOperator_measurable {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) :
    Measurable (rieszSecondL2MeasurableOperator hL2 u) := by
  exact rieszSecondLpMeasurableRepresentative_measurable _

theorem rieszSecondL2MeasurableOperator_ae_eq_extension {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) :
    rieszSecondL2MeasurableOperator hL2 u =ᵐ[volume]
      rieszSecondL2Extension hL2 u := by
  exact rieszSecondLpMeasurableRepresentative_ae_eq _ |>.symm

theorem rieszSecondL2MeasurableOperator_add_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u v : rieszSecondL2) :
    rieszSecondL2MeasurableOperator hL2 (u + v) =ᵐ[volume]
      rieszSecondL2MeasurableOperator hL2 u +
        rieszSecondL2MeasurableOperator hL2 v := by
  calc
    rieszSecondL2MeasurableOperator hL2 (u + v) =ᵐ[volume]
        ((rieszSecondL2Extension hL2 (u + v) : rieszSecondL2) : Vec3 → ℝ) :=
      rieszSecondL2MeasurableOperator_ae_eq_extension hL2 _
    _ =ᵐ[volume]
        ((rieszSecondL2Extension hL2 u : rieszSecondL2) : Vec3 → ℝ) +
          ((rieszSecondL2Extension hL2 v : rieszSecondL2) : Vec3 → ℝ) := by
      rw [map_add]
      exact Lp.coeFn_add _ _
    _ =ᵐ[volume] rieszSecondL2MeasurableOperator hL2 u +
          rieszSecondL2MeasurableOperator hL2 v := by
      exact (rieszSecondLpMeasurableRepresentative_ae_eq _).add
        (rieszSecondLpMeasurableRepresentative_ae_eq _)

theorem rieszSecondL2MeasurableOperator_smul_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (c : ℝ) (u : rieszSecondL2) :
    rieszSecondL2MeasurableOperator hL2 (c • u) =ᵐ[volume]
      c • rieszSecondL2MeasurableOperator hL2 u := by
  calc
    rieszSecondL2MeasurableOperator hL2 (c • u) =ᵐ[volume]
        ((rieszSecondL2Extension hL2 (c • u) : rieszSecondL2) : Vec3 → ℝ) :=
      rieszSecondL2MeasurableOperator_ae_eq_extension hL2 _
    _ =ᵐ[volume] c •
        ((rieszSecondL2Extension hL2 u : rieszSecondL2) : Vec3 → ℝ) := by
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    _ =ᵐ[volume] c • rieszSecondL2MeasurableOperator hL2 u := by
      exact (rieszSecondLpMeasurableRepresentative_ae_eq _).const_smul c

theorem rieszSecondL2MeasurableOperator_eLpNorm_le {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) :
    eLpNorm (rieszSecondL2MeasurableOperator hL2 u)
        (2 : ℝ≥0∞) volume ≤ eLpNorm (u : Vec3 → ℝ)
        (2 : ℝ≥0∞) volume := by
  have hae := rieszSecondL2MeasurableOperator_ae_eq_extension hL2 u
  have hnorm := rieszSecondL2Extension_norm_le hL2 u
  rw [Lp.norm_def, Lp.norm_def] at hnorm
  rw [eLpNorm_congr_ae hae]
  apply (ENNReal.toReal_le_toReal
    (Lp.eLpNorm_ne_top (rieszSecondL2Extension hL2 u))
    (Lp.eLpNorm_ne_top u)).mp
  exact hnorm

theorem rieszSecondL2MeasurableOperator_l2_bound {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) :
    (∫⁻ x, absE (rieszSecondL2MeasurableOperator hL2 u) x ^ (2 : ℕ)) ≤
      ∫⁻ x, absE (u : Vec3 → ℝ) x ^ (2 : ℕ) := by
  have hTae : AEStronglyMeasurable
      (rieszSecondL2MeasurableOperator hL2 u) volume :=
    (rieszSecondL2MeasurableOperator_measurable hL2 u).aestronglyMeasurable
  have hUae : AEStronglyMeasurable (u : Vec3 → ℝ) volume :=
    Lp.aestronglyMeasurable u
  have hTpow := lintegral_rpow_enorm_eq_rpow_eLpNorm'
    (f := rieszSecondL2MeasurableOperator hL2 u) (μ := volume)
    (q := (2 : ℝ)) (by norm_num)
  have hUpow := lintegral_rpow_enorm_eq_rpow_eLpNorm'
    (f := (u : Vec3 → ℝ)) (μ := volume)
    (q := (2 : ℝ)) (by norm_num)
  have hTeq := eLpNorm_eq_eLpNorm' (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hTae
  have hUeq := eLpNorm_eq_eLpNorm' (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hUae
  have hnorm := rieszSecondL2MeasurableOperator_eLpNorm_le hL2 u
  have hTeq' : eLpNorm (rieszSecondL2MeasurableOperator hL2 u)
      (2 : ℝ≥0∞) volume =
      eLpNorm' (rieszSecondL2MeasurableOperator hL2 u) (2 : ℝ) volume := by
    simpa only [show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) by norm_num] using hTeq
  have hUeq' : eLpNorm (u : Vec3 → ℝ)
      (2 : ℝ≥0∞) volume = eLpNorm' (u : Vec3 → ℝ) (2 : ℝ) volume := by
    simpa only [show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) by norm_num] using hUeq
  calc
    (∫⁻ x, absE (rieszSecondL2MeasurableOperator hL2 u) x ^ (2 : ℕ)) =
        (eLpNorm' (rieszSecondL2MeasurableOperator hL2 u) (2 : ℝ) volume) ^
          (2 : ℕ) := by
      norm_num at hTpow
      simpa only [absE, Real.enorm_eq_ofReal_abs] using hTpow
    _ = (eLpNorm (rieszSecondL2MeasurableOperator hL2 u)
        (2 : ℝ≥0∞) volume) ^ (2 : ℕ) := by rw [hTeq'.symm]
    _ ≤ (eLpNorm (u : Vec3 → ℝ) (2 : ℝ≥0∞) volume) ^ (2 : ℕ) := by
      exact pow_le_pow_left' hnorm 2
    _ = (eLpNorm' (u : Vec3 → ℝ) (2 : ℝ) volume) ^ (2 : ℕ) := by
      rw [hUeq']
    _ = ∫⁻ x, absE (u : Vec3 → ℝ) x ^ (2 : ℕ) := by
      norm_num at hUpow
      simpa only [absE, Real.enorm_eq_ofReal_abs] using hUpow.symm

theorem rieszSecondL2MeasurableOperator_smooth_global_bound {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    (∫⁻ x, absE (rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc))) x ^
        (2 : ℕ)) ≤
      ∫⁻ x, absE F x ^ (2 : ℕ) := by
  obtain ⟨hmem, hEq⟩ := rieszSecondL2Extension_smooth_hessian hL2 hF hFc
  have hfun : rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc)) =ᵐ[volume]
      (fun x => mixedSecond (pressureNewtonianPotential F) i j x) := by
    calc
      rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc)) =ᵐ[volume]
          ((rieszSecondL2Extension hL2
            (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc)) :
              rieszSecondL2) : Vec3 → ℝ) :=
        rieszSecondL2MeasurableOperator_ae_eq_extension hL2 _
      _ =ᵐ[volume] (MemLp.toLp
          (mixedSecond (pressureNewtonianPotential F) i j) hmem : Vec3 → ℝ) := by
        rw [hEq]
      _ =ᵐ[volume] (fun x => mixedSecond (pressureNewtonianPotential F) i j x) :=
        hmem.coeFn_toLp
  have hfun' : (fun x =>
      absE (rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc))) x ^ (2 : ℕ)) =ᵐ[volume]
      (fun x => absE (mixedSecond (pressureNewtonianPotential F) i j) x ^ (2 : ℕ)) := by
    filter_upwards [hfun] with x hx
    simp only [absE, hx]
  rw [lintegral_congr_ae hfun']
  simpa only [absE, Real.enorm_eq_ofReal_abs, sq_abs, one_pow,
    ENNReal.ofReal_one, one_mul] using
    (riesz_second_l2_bound_global hF hFc i j)

/- The weak endpoint is stated only for an `L¹ ∩ L²` input.  The fields are
   precisely the good/bad Calderón–Zygmund certificate consumed by the
   unconditional assembly in `RieszSecond.lean`; the displayed operator is
   always the `L²` representative of the fixed input class. -/
theorem rieszSecondL2_weak_type_of_cz_certificate
    {i j : Fin 3} {F : Vec3 → ℝ} {level C₂ A : ℝ} {C_H : ℝ≥0∞}
    (hL2 : RieszSecondL2Input i j) (hF : Integrable F)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (hlevel : 0 < level)
    (hA : 0 ≤ A) (hAeq : dyadicL1Norm F = ENNReal.ofReal A)
    {G B : CZDecomposition F level → Vec3 → ℝ}
    (hdecomp : ∀ D : CZDecomposition F level, ∀ x,
      rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x =
        G D x + B D x)
    (henergy : ∀ D : CZDecomposition F level,
      ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * level * A)
    (hgoodL2 : ∀ D : CZDecomposition F level,
      Integrable (fun x => G D x ^ (2 : ℕ)) volume ∧
      (∫ x, G D x ^ (2 : ℕ)) ≤ C₂ ^ 2 *
        ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ))
    (hbad : ∀ D : CZDecomposition F level,
      ∃ Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ,
        Integrable (B D) volume ∧
        (∀ᵐ x ∂(volume.restrict
            (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
          ENNReal.ofReal |B D x| ≤
            ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|) ∧
        (∀ Q : {Q // Q ∈ D.cubes},
          AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
            (volume.restrict
              (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ)) ∧
        (∀ Q : {Q // Q ∈ D.cubes},
          (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
            ENNReal.ofReal |Tbad Q x|) ≤
            C_H * ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicBadPart F Q.1 x|)) :
    volume {x | level < |rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp F hF₂) x|} ≤
      ENNReal.ofReal (8 * C₂ ^ 2 * level / (level / 2) ^ 2) *
          ENNReal.ofReal A +
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal level) +
        (C_H * (2 * ENNReal.ofReal A)) /
          ENNReal.ofReal (level / 2) := by
  exact rieszSecond_weak_type_unconditional hF hlevel hA hAeq
    (T := rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂))
    hdecomp henergy hgoodL2 hbad

/- A per-input certificate packages the data needed by the dyadic assembly.
   Its kernel constant is the one supplied by the second Newtonian derivative. -/
structure RieszSecondL2CZCertificate {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (F : Vec3 → ℝ)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (level : ℝ) where
  A : ℝ
  hA : 0 ≤ A
  hAeq : dyadicL1Norm F = ENNReal.ofReal A
  G : CZDecomposition F level → Vec3 → ℝ
  B : CZDecomposition F level → Vec3 → ℝ
  hdecomp : ∀ D : CZDecomposition F level, ∀ x,
      rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp F hF₂) x =
      G D x + B D x
  henergy : ∀ D : CZDecomposition F level,
    ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * level * A
  hgoodL2 : ∀ D : CZDecomposition F level,
    Integrable (fun x => G D x ^ (2 : ℕ)) volume ∧
    (∫ x, G D x ^ (2 : ℕ)) ≤
      (1 : ℝ) ^ 2 * ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)
  hbad : ∀ D : CZDecomposition F level,
    ∃ Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ,
      Integrable (B D) volume ∧
      (∀ᵐ x ∂(volume.restrict
          (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
        ENNReal.ofReal |B D x| ≤
          ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
          (volume.restrict
            (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ)) ∧
        (∀ Q : {Q // Q ∈ D.cubes},
          (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
            ENNReal.ofReal |Tbad Q x|) ≤
          ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
            ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicBadPart F Q.1 x|)

def rieszSecondWeakTypeConstant : ℝ :=
  32 + 32 * Real.pi * Real.sqrt 3 +
    256 * Real.pi * rieszSecondKernelC₂

theorem rieszSecondKernelC_H :
    ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) =
      ENNReal.ofReal 1152 := by
  congr 1
  dsimp [rieszSecondKernelC₂]
  field_simp [Real.pi_ne_zero]
  ring

def rieszSecondL2RawOperator {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (f : Vec3 → ℝ) : Vec3 → ℝ := by
  classical
  exact if hf : MemLp f (2 : ℝ≥0∞) volume then
    rieszSecondL2MeasurableOperator hL2 (MemLp.toLp f hf)
  else 0

theorem rieszSecondL2RawOperator_measurable {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    Measurable (rieszSecondL2RawOperator hL2 f) := by
  classical
  simp only [rieszSecondL2RawOperator, hf, ↓reduceDIte]
  exact rieszSecondL2MeasurableOperator_measurable hL2 _

theorem rieszSecondL2RawOperator_ae_eq {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    rieszSecondL2RawOperator hL2 f =ᵐ[volume]
      rieszSecondL2MeasurableOperator hL2 (MemLp.toLp f hf) := by
  classical
  simp only [rieszSecondL2RawOperator, hf, ↓reduceDIte]
  exact EventuallyEq.rfl

private theorem rieszSecond_weak_constant_bound
    {A l : ℝ} (hA : 0 ≤ A) (hl : 0 < l) {M : ℝ≥0∞}
    (hM : M ≤ ENNReal.ofReal (8 * (1 : ℝ) ^ 2 * l / (l / 2) ^ 2) *
          ENNReal.ofReal A +
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal l) +
        (ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          (2 * ENNReal.ofReal A)) /
          ENNReal.ofReal (l / 2)) :
    M ≤ ENNReal.ofReal rieszSecondWeakTypeConstant * ENNReal.ofReal A /
      ENNReal.ofReal l := by
  calc
    M ≤ ENNReal.ofReal (8 * (1 : ℝ) ^ 2 * l / (l / 2) ^ 2) *
          ENNReal.ofReal A +
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal l) +
        (ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          (2 * ENNReal.ofReal A)) /
          ENNReal.ofReal (l / 2) := hM
    _ = ENNReal.ofReal rieszSecondWeakTypeConstant * ENNReal.ofReal A /
        ENNReal.ofReal l := by
      dsimp [rieszSecondWeakTypeConstant]
      have hlne : l ≠ 0 := ne_of_gt hl
      rw [show 8 * (1 : ℝ) ^ 2 * l / (l / 2) ^ 2 = 32 / l by
        norm_num [pow_two]
        field_simp
        norm_num]
      have hfirst : ENNReal.ofReal (32 / l) * ENNReal.ofReal A =
          ENNReal.ofReal ((32 / l) * A) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 32 / l)]
      have hsecond : ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal l) =
          ENNReal.ofReal ((32 * Real.pi * Real.sqrt 3) * (A / l)) := by
        rw [← ENNReal.ofReal_div_of_pos hl]
        rw [← ENNReal.ofReal_mul (by positivity :
          0 ≤ 32 * Real.pi * Real.sqrt 3)]
      have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
      have hthird : (ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          (2 * ENNReal.ofReal A)) / ENNReal.ofReal (l / 2) =
          ENNReal.ofReal ((64 * Real.pi * rieszSecondKernelC₂ * (2 * A)) /
            (l / 2)) := by
        have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
        rw [htwo, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)),
          ← ENNReal.ofReal_mul (by positivity :
            0 ≤ 64 * Real.pi * rieszSecondKernelC₂),
          ← ENNReal.ofReal_div_of_pos (by positivity : 0 < l / 2)]
      rw [hfirst, hsecond, hthird]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have htarget : ENNReal.ofReal (32 + 32 * Real.pi * Real.sqrt 3 +
          256 * Real.pi * rieszSecondKernelC₂) * ENNReal.ofReal A /
            ENNReal.ofReal l =
          ENNReal.ofReal ((32 + 32 * Real.pi * Real.sqrt 3 +
            256 * Real.pi * rieszSecondKernelC₂) * A / l) := by
        rw [← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_div_of_pos hl]
      rw [htarget]
      congr 1
      field_simp [hlne]
      ring_nf

/- This is the restricted weak endpoint in the exact form consumed by the
   L²-class interpolation theorem.  The input certificate is supplied by the
   dyadic decomposition and the exterior kernel estimate. -/
theorem rieszSecondL2_restricted_weak_type {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hcertificate : ∀ {F : Vec3 → ℝ} {level : ℝ}
      (_hFmeas : Measurable F) (_hFint : Integrable F)
      (hF₂ : MemLp F (2 : ℝ≥0∞) volume), 0 < level →
      RieszSecondL2CZCertificate hL2 F hF₂ level) :
    ∀ f, Measurable f → Integrable f →
      MemLp f (2 : ℝ≥0∞) volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l := by
  intro f hf hfi hf₂ l hl
  let cert := hcertificate hf hfi hf₂ hl
  have hbound := rieszSecondL2_weak_type_of_cz_certificate
    (C₂ := (1 : ℝ))
    (C_H := ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂))
    hL2 hfi hf₂ hl
    cert.hA cert.hAeq cert.hdecomp cert.henergy cert.hgoodL2 cert.hbad
  have hbound' := rieszSecond_weak_constant_bound cert.hA hl hbound
  have hnorm : (∫⁻ x, absE f x) = ENNReal.ofReal cert.A := by
    rw [← cert.hAeq]
    rfl
  rw [hnorm]
  simpa only [rieszSecondL2RawOperator, hf₂, ↓reduceDIte,
    rieszSecondWeakTypeConstant, dyadicL1Norm] using hbound'

end CKN.Foundation.Euclidean
