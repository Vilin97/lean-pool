/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.Recognition.Smale7

/-!
# Hopf problem: toric · diagonal quotient 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem DiagonalQuotient.quotient_smul_fst {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] (g : G) (b : B) (f : F) :
    quotient G B F (g • b, f) = quotient G B F (b, g⁻¹ • f) := by
  apply (quotient_eq_iff G B F _ _).mpr
  exact ⟨g, by simp⟩

private def CuspQuotient.sectionCoordinates (t : ℂ) : ToricCharts.CoordinateSpace 3 :=
  ![t, 1, 1]

@[simp]
private theorem CuspQuotient.time_sectionCoordinates (t : ℂ) :
    ToricFan.Triangle.time (sectionCoordinates t) = t := by
  simp [ToricFan.Triangle.time, sectionCoordinates]

private theorem CuspQuotient.sectionCoordinates_holomorphic : ContDiff ℂ ω sectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

private def CuspQuotient.sectionLift (ε : ℝ) (t : disc ε) : ToricSpace.Tube (disc ε) :=
  ⟨ToricSpace.inclusion ToricSpace.referenceTriangle (sectionCoordinates t),
    by
    change
      ToricSpace.time (ToricSpace.inclusion ToricSpace.referenceTriangle (sectionCoordinates t)) ∈
        disc ε
    simpa only [ToricSpace.time_inclusion, time_sectionCoordinates] using t.2⟩

private theorem CuspQuotient.sectionLift_continuous (ε : ℝ) : Continuous (sectionLift ε) :=
  (((ToricSpace.inclusion_openEmbedding ToricSpace.referenceTriangle).continuous.comp
            sectionCoordinates_holomorphic.continuous).comp
        continuous_subtype_val).subtype_mk
    _

private def CuspQuotient.zeroSection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    disc ε → QuotientSpace C ε :=
  quotientMap C ε ∘ sectionLift ε

@[simp]
private theorem CuspQuotient.projection_zeroSection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (t : disc ε) : projection C ε (zeroSection C ε t) = t := by
  change
    ToricSpace.time (ToricSpace.inclusion ToricSpace.referenceTriangle (sectionCoordinates t)) = t
  simp

private theorem CuspQuotient.zeroSection_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (zeroSection C ε) :=
  (quotientMap_continuous C ε).comp (sectionLift_continuous ε)

private def CuspQuotient.discLoopContraction {ε : ℝ} {z : disc ε} (p : Path z z) :
    p.Homotopy (Path.refl z)
    where
  toFun
    u :=
    ⟨(1 - (u.1 : ℝ)) • (p u.2 : ℂ) + (u.1 : ℝ) • (z : ℂ),
      (convex_ball (0 : ℂ) ε) (p u.2).2 z.2 (sub_nonneg.mpr u.1.2.2) u.1.2.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by fun_prop
  map_zero_left t := by apply Subtype.ext; simp
  map_one_left t := by apply Subtype.ext; simp
  prop' s t
    ht := by
    apply Subtype.ext
    change (1 - (s : ℝ)) • (p t : ℂ) + (s : ℝ) • (z : ℂ) = (p t : ℂ)
    rcases ht with rfl | rfl <;> simp <;> ring

private def
    DiagonalQuotient.zeroSection {G B F : Type*} [Group G] [MulAction G B] [MulAction G F] (c : F)
    (hc : ∀ g : G, g • c = c) : BaseSpace G B → Space G B F :=
  Quotient.lift (fun b : B => quotient G B F (b, c))
    (by
      rintro b b' ⟨g, hg⟩
      exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg (hc g)⟩)

private theorem DiagonalQuotient.zeroSection_continuous {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) (hc : ∀ g : G, g • c = c) :
    Continuous (zeroSection (B := B) c hc) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr
    ((quotient_continuous G B F).comp (continuous_id.prodMk continuous_const))

@[simp]
private theorem DiagonalQuotient.projection_zeroSection {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] (c : F) (hc : ∀ g : G, g • c = c) (x : BaseSpace G B) :
    projection G B F (zeroSection c hc x) = x := by
  induction x using Quotient.inductionOn with
  | h b => rfl

private def DiagonalQuotient.fibreFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    FundamentalGroup F c →* FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ c

private def DiagonalQuotient.projectionFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    FundamentalGroup (Space G B F) (fibreInclusion G B F b c) →*
      FundamentalGroup (BaseSpace G B) (baseQuotient G B b) :=
  FundamentalGroup.map ⟨projection G B F, projection_continuous G B F⟩ (fibreInclusion G B F b c)

private def DiagonalQuotient.sectionFundamentalGroupHom {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F) (hc : ∀ g : G, g • c = c)
    (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →*
      FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨zeroSection c hc, zeroSection_continuous c hc⟩ (baseQuotient G B b)

private theorem
    DiagonalQuotient.projectionFundamentalGroupHom_comp_section {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (c : F)
    (hc : ∀ g : G, g • c = c) (b : B) :
    (projectionFundamentalGroupHom (G := G) b c).comp (sectionFundamentalGroupHom c hc b) =
      MonoidHom.id (FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) := by
  apply DFunLike.ext
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk
    γ =>
    change
      Path.Homotopic.Quotient.mk
          ((γ.map (zeroSection_continuous c hc)).map (projection_continuous G B F)) =
        Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact projection_zeroSection c hc (γ t)

@[simp]
private theorem DiagonalQuotient.projectionFundamentalGroupHom_fibre {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F)
    (γ : FundamentalGroup F c) :
    projectionFundamentalGroupHom (G := G) b c (fibreFundamentalGroupHom b c γ) = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk
    γ =>
    change
      Path.Homotopic.Quotient.mk
          ((γ.map (fibreInclusion_continuous G B F b)).map (projection_continuous G B F)) =
        Path.Homotopic.Quotient.mk (Path.refl (baseQuotient G B b))
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl

private theorem DiagonalQuotient.fibreFundamentalGroupHom_range_le_ker {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range ≤
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  rintro γ ⟨δ, rfl⟩
  exact projectionFundamentalGroupHom_fibre b c δ

private def
    DiagonalQuotient.deckTransportHom {G B : Type*} [Group G] [MulAction G B] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →* G :=
  (MulEquiv.inv' G).symm.toMonoidHom.comp (hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩)

private theorem DiagonalQuotient.deckTransportHom_monodromy {G B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (γ : FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) :
    (deckTransportHom hq b γ)⁻¹ • b = (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) := by
  change ((hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩ γ).unop⁻¹)⁻¹ • b = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

private def DiagonalQuotient.fibreActionFundamentalGroupHom {G F : Type*} [Group G] [MulAction G F]
    [TopologicalSpace F] [ContinuousConstSMul G F] (c : F) (hc : ∀ g : G, g • c = c) (g : G) :
    FundamentalGroup F c →* FundamentalGroup F c :=
  FundamentalGroup.mapOfEq ⟨fun x : F => g • x, ContinuousConstSMul.continuous_const_smul g⟩
    (hc g)

private theorem DiagonalQuotient.quotient_loop_lift_of_projection_eq_refl {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F)
    (γ : Path.Homotopic.Quotient (fibreInclusion G B F b c) (fibreInclusion G B F b c))
    (hγ :
      γ.map ⟨projection G B F, projection_continuous G B F⟩ =
        Path.Homotopic.Quotient.refl (baseQuotient G B b)) :
    ∃ δ : Path.Homotopic.Quotient (b, c) (b, c),
      δ.map ⟨quotient G B F, quotient_continuous G B F⟩ = γ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    let cov := (quotientCoveringMap (F := F) hq).isCoveringMap
    let L : C(unitInterval, B × F) := cov.liftPath γ (b, c) γ.source
    let γb : Path (baseQuotient G B b) (baseQuotient G B b) := γ.map (projection_continuous G B F)
    let Lb : C(unitInterval, B) := ⟨fun t => (L t).1, continuous_fst.comp L.continuous⟩
    have hLb : Lb = hq.isCoveringMap.liftPath γb b γb.source := by
      apply (hq.isCoveringMap.eq_liftPath_iff' γb.source).mpr
      constructor
      · funext t
        exact congrArg (projection G B F) (congrFun (cov.liftPath_lifts γ (b, c) γ.source) t)
      · exact congrArg Prod.fst (cov.liftPath_zero γ (b, c) γ.source)
    have hnull : γb.Homotopic (Path.refl (baseQuotient G B b)) := by
      apply Path.Homotopic.Quotient.eq.mp
      exact hγ
    have hbaseEnd : hq.isCoveringMap.liftPath γb b γb.source 1 = b := by
      have h := hq.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel hnull b γb.source rfl
      have hc : hq.isCoveringMap.liftPath (Path.refl (baseQuotient G B b)) b rfl 1 = b := by
        exact
          congrArg (fun p : C(unitInterval, B) => p 1)
            (hq.isCoveringMap.liftPath_const (e := b) rfl)
      exact h.trans hc
    have hfirst : (L 1).1 = b := (congrArg (fun p : C(unitInterval, B) => p 1) hLb).trans hbaseEnd
    have hquot : quotient G B F (L 1) = quotient G B F (b, c) :=
      (congrFun (cov.liftPath_lifts γ (b, c) γ.source) 1).trans γ.target
    have hsecond : (L 1).2 = c := by
      apply fibreInclusion_injective (F := F) hq b
      have hp : (b, (L 1).2) = L 1 := Prod.ext hfirst.symm rfl
      exact (congrArg (quotient G B F) hp).trans hquot
    have hlast : L 1 = (b, c) := Prod.ext hfirst hsecond
    let δ : Path (b, c) (b, c) := ⟨L, cov.liftPath_zero γ (b, c) γ.source, hlast⟩
    refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
    change
      Path.Homotopic.Quotient.mk (δ.map (quotient_continuous G B F)) =
        Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact congrFun (cov.liftPath_lifts γ (b, c) γ.source) t

private theorem DiagonalQuotient.product_loop_eq_vertical_of_fst_eq_refl {B F : Type*}
    [TopologicalSpace B] [TopologicalSpace F] (b : B) (c : F)
    (α : Path.Homotopic.Quotient (b, c) (b, c)) (h : α.map ⟨Prod.fst, continuous_fst⟩ = .refl b) :
    α =
      (α.map ⟨Prod.snd, continuous_snd⟩).map
        ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
  have hv (β : Path.Homotopic.Quotient c c) :
    Path.Homotopic.prod (.refl b) β =
      β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  calc
    α =
        Path.Homotopic.prod (α.map ⟨Prod.fst, continuous_fst⟩)
          (α.map ⟨Prod.snd, continuous_snd⟩) :=
      (Path.Homotopic.prod_projLeft_projRight α).symm
    _ = Path.Homotopic.prod (.refl b) (α.map ⟨Prod.snd, continuous_snd⟩) := by rw [h]
    _ =
        (α.map ⟨Prod.snd, continuous_snd⟩).map
          ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩ :=
      hv _

private theorem
    DiagonalQuotient.product_vertical_loop_map_injective {B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] (b : B) (c : F) :
    Function.Injective
      (fun β : Path.Homotopic.Quotient c c =>
        β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩) := by
  have hleft (β : Path.Homotopic.Quotient c c) :
    (β.map ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨Prod.snd, continuous_snd⟩ =
      β := by
    induction β using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  intro α β h
  have hs :=
    congrArg (fun γ : Path.Homotopic.Quotient (b, c) (b, c) => γ.map ⟨Prod.snd, continuous_snd⟩) h
  exact (hleft α).symm.trans (hs.trans (hleft β))

private theorem DiagonalQuotient.fibreFundamentalGroupHom_injective {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F) :
    Function.Injective (fibreFundamentalGroupHom (G := G) b c) := by
  intro α β h
  apply product_vertical_loop_map_injective b c
  apply (quotient_isCoveringMap (F := F) hq).injective_path_homotopic_map (b, c) (b, c)
  change
    (Path.Homotopic.Quotient.map α
            ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨quotient G B F, quotient_continuous G B F⟩ =
      (Path.Homotopic.Quotient.map β
            ⟨fun f : F => (b, f), continuous_const.prodMk continuous_id⟩).map
        ⟨quotient G B F, quotient_continuous G B F⟩
  rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
  exact h

private theorem DiagonalQuotient.fibreFundamentalGroupHom_range_eq_ker {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range =
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  apply le_antisymm (fibreFundamentalGroupHom_range_le_ker b c)
  intro γ hγ
  change
    Path.Homotopic.Quotient.map γ ⟨projection G B F, projection_continuous G B F⟩ =
      Path.Homotopic.Quotient.refl (baseQuotient G B b) at hγ
  obtain ⟨α, hα⟩ := quotient_loop_lift_of_projection_eq_refl hq b c γ hγ
  have hfst : α.map ⟨Prod.fst, continuous_fst⟩ = Path.Homotopic.Quotient.refl b := by
    apply hq.isCoveringMap.injective_path_homotopic_map b b
    change
      (α.map ⟨Prod.fst, continuous_fst⟩).map ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        Path.Homotopic.Quotient.refl (baseQuotient G B b)
    have hs :
      (α.map ⟨Prod.fst, continuous_fst⟩).map ⟨baseQuotient G B, baseQuotient_continuous G B⟩ =
        (α.map ⟨quotient G B F, quotient_continuous G B F⟩).map
          ⟨projection G B F, projection_continuous G B F⟩ := by
      rw [← Path.Homotopic.Quotient.map_comp, ← Path.Homotopic.Quotient.map_comp]
      rfl
    exact
      hs.trans
        ((congrArg
              (fun η :
                  Path.Homotopic.Quotient (fibreInclusion G B F b c) (fibreInclusion G B F b c) =>
                η.map ⟨projection G B F, projection_continuous G B F⟩)
              hα).trans
          hγ)
  refine ⟨α.map ⟨Prod.snd, continuous_snd⟩, ?_⟩
  have hv :=
    congrArg
      (fun η : Path.Homotopic.Quotient (b, c) (b, c) =>
        η.map ⟨quotient G B F, quotient_continuous G B F⟩)
      (product_loop_eq_vertical_of_fst_eq_refl b c α hfst)
  rw [← Path.Homotopic.Quotient.map_comp] at hv
  exact hv.symm.trans hα

private def
    DiagonalQuotient.liftedFibreHomotopy {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (γ : Path (baseQuotient G B b) (baseQuotient G B b)) (g : G)
    (hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ : C(F, Space G B F))
      ⟨fun f : F => fibreInclusion G B F b (g • f),
        (fibreInclusion_continuous G B F b).comp (ContinuousConstSMul.continuous_const_smul g)⟩
    where
  toFun p := quotient G B F (hq.isCoveringMap.liftPath γ b γ.source p.1, p.2)
  continuous_toFun :=
    (quotient_continuous G B F).comp
      (((hq.isCoveringMap.liftPath γ b γ.source).continuous.comp continuous_fst).prodMk
        continuous_snd)
  map_zero_left
    f := by
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source 0, f) = quotient G B F (b, f)
    rw [hq.isCoveringMap.liftPath_zero]
  map_one_left
    f := by
    change
      quotient G B F ((hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B), f) =
        quotient G B F (b, g • f)
    rw [hend, quotient_smul_fst, inv_inv]

private theorem DiagonalQuotient.fundamentalGroup_conjugation_of_homotopy {F E : Type*}
    [TopologicalSpace F] [TopologicalSpace E] (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁) (c : F)
    (e : E) (h₀ : f₀ c = e) (h₁ : f₁ c = e) (v : FundamentalGroup F c) :
    let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
    s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ = FundamentalGroup.mapOfEq f₁ h₁ v := by
  let s : FundamentalGroup E e := .mk ((H.evalAt c).cast h₀.symm h₁.symm)
  change s * FundamentalGroup.mapOfEq f₀ h₀ v * s⁻¹ = FundamentalGroup.mapOfEq f₁ h₁ v
  have hsquare : s * FundamentalGroup.mapOfEq f₀ h₀ v = FundamentalGroup.mapOfEq f₁ h₁ v * s := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
    simp only [s, FundamentalGroup.mul_def, FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_trans]
    apply Path.Homotopic.Quotient.eq.mpr
    have hp := (Path.Homotopic.map_trans_evalAt H p).pathCast h₀.symm h₁.symm
    rw [Path.cast_trans (p.map f₀.continuous) (H.evalAt c) h₀.symm h₀.symm h₁.symm,
      Path.cast_trans (H.evalAt c) (p.map f₁.continuous) h₀.symm h₁.symm h₁.symm] at hp
    exact hp
  rw [hsquare, mul_inv_cancel_right]

public
theorem DiagonalQuotient.fundamentalGroup_mapOfEq_comp {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (a : A) (b : B) (c : C)
    (hf : f a = b) (hg : g b = c) (v : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) v =
      FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf v) := by
  simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
    Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.cast_cast]

private theorem
    DiagonalQuotient.sectionFundamentalGroupHom_conjugate_fibre {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (c : F)
    (hc : ∀ g : G, g • c = c) (b : B) (β : FundamentalGroup (BaseSpace G B) (baseQuotient G B b))
    (v : FundamentalGroup F c) :
    sectionFundamentalGroupHom c hc b β * fibreFundamentalGroupHom b c v *
        (sectionFundamentalGroupHom c hc b β)⁻¹ =
      fibreFundamentalGroupHom b c
        (fibreActionFundamentalGroupHom c hc (deckTransportHom hq b β) v) := by
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective β
  let g : G := deckTransportHom hq b (.mk γ)
  have hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b :=
    (deckTransportHom_monodromy hq b (.mk γ)).symm
  let i : C(F, Space G B F) := ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩
  let a : C(F, F) := ⟨fun f : F => g • f, ContinuousConstSMul.continuous_const_smul g⟩
  let H : i.Homotopy (i.comp a) := liftedFibreHomotopy (F := F) hq b γ g hend
  have h₁ : (i.comp a) c = i c := congrArg i (hc g)
  let s : FundamentalGroup (Space G B F) (i c) := .mk ((H.evalAt c).cast rfl h₁.symm)
  have hs : s = sectionFundamentalGroupHom c hc b (.mk γ) := by
    change
      Path.Homotopic.Quotient.mk ((H.evalAt c).cast rfl h₁.symm) =
        Path.Homotopic.Quotient.mk (γ.map (zeroSection_continuous c hc))
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source t, c) = zeroSection c hc (γ t)
    have hlift : baseQuotient G B (hq.isCoveringMap.liftPath γ b γ.source t) = γ t :=
      congrFun (hq.isCoveringMap.liftPath_lifts γ b γ.source) t
    exact congrArg (zeroSection c hc) hlift
  have hi (w : FundamentalGroup F c) :
    FundamentalGroup.mapOfEq i rfl w = fibreFundamentalGroupHom b c w := by
    rw [FundamentalGroup.mapOfEq_apply]
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  have hterminal :
    FundamentalGroup.mapOfEq (i.comp a) h₁ v =
      fibreFundamentalGroupHom b c (fibreActionFundamentalGroupHom c hc g v) := by
    have hcomp := fundamentalGroup_mapOfEq_comp a i c c (i c) (hc g) rfl v
    rw [hi] at hcomp
    exact hcomp
  have hconj := fundamentalGroup_conjugation_of_homotopy i (i.comp a) H c (i c) rfl h₁ v
  change
    s * FundamentalGroup.mapOfEq i rfl v * s⁻¹ = FundamentalGroup.mapOfEq (i.comp a) h₁ v at hconj
  rw [hs, hi, hterminal] at hconj
  exact hconj

end Mathoverflow1973

end
