/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology4
public import LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology4
import all LeanPool.HopfProblem.Elliptic.Core3

/-!
# Hopf problem: homology of x · threefold gluing 1

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

private def
    ThreefoldHomologyCuspFibre.fibreCentralHomotopy (D : SpecialPeriods.CuspFamily.Data) (η : ℝ)
    (hη : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη).comp R))
    (t : ℂ) (htη : ‖t‖ ≤ η) :
    (actualFibreInclusion D t).Homotopy
      ((ThreefoldHomologyFinitenessCusp.fullCentralInclusion D).comp
        (R.comp (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη)))
    where
  toFun
    p :=
    (H (p.1, CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      (H.continuous.comp
        (continuous_fst.prodMk
          ((CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t
                htη).continuous.comp
            continuous_snd)))
  map_zero_left
    q :=
    congrArg Subtype.val
      (H.map_zero_left
        (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη q))
  map_one_left
    q :=
    congrArg Subtype.val
      (H.map_one_left (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη q))

private theorem ThreefoldHomologyCuspFibre.exists_smallFibreInclusion_homology_surjective
    (D : SpecialPeriods.CuspFamily.Data) :
    ∃ δ : ℝ,
      0 < δ ∧
        δ < D.radius ∧
          ∀ (t : ℂ),
            t ≠ 0 →
              ‖t‖ ≤ δ →
                ∀ n : ℕ,
                  Function.Surjective
                    (SingularMayerVietoris.singularHomologyMap (actualFibreInclusion D t) n) := by
  obtain ⟨δs, hδs, hδsr, _hδs1, hspec⟩ :=
    CuspCentralHomology.exists_actual_specialization_homology D.correction D.radius D.radius_pos
      D.holomorphic
  obtain ⟨δr, hδr, _hδrr, _hδr1, hret⟩ :=
    CuspCentralHomology.exists_controlled_retraction_all_levels D.correction D.radius_pos
      D.holomorphic
  let δ := Min.min δs δr
  have hδ : 0 < δ := lt_min hδs hδr
  have hδradius : δ < D.radius := (min_le_left δs δr).trans_lt hδsr
  refine ⟨δ, hδ, hδradius, ?_⟩
  intro t ht htδ n
  obtain ⟨E, hE⟩ := hspec t ht (htδ.trans (min_le_left δs δr))
  obtain ⟨hc, _hmarked, hsurj, _h2, _h3⟩ := hE δ (min_le_left δs δr) htδ hδradius
  let c :
    C(CuspControlledRetraction.ActualQuotientFibre D.correction D.radius t,
      CuspRetraction.QuotientCentralFibre D.correction D.radius) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse D.correction D.radius D.radius_pos
        hδradius t ht htδ,
      hc⟩
  obtain ⟨R, _hR, H, _hmono, hc', hend, _hall⟩ := hret δ hδ (min_le_right δs δr) hδradius t ht htδ
  have hend' :
    R.comp (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius δ t htδ) = c := hend
  have hm :
    SingularMayerVietoris.singularHomologyMap (actualFibreInclusion D t) n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomologyFinitenessCusp.fullCentralInclusion D) n).comp
        (SingularMayerVietoris.singularHomologyMap c n) := by
    rw [PeriodTorusHigherHomology.homotopy_homologyMap
        (fibreCentralHomotopy D δ hδ.le R H.toHomotopy t htδ) n,
      hend', PeriodTorusHigherHomology.singularHomologyMap_comp]
  rw [hm, ← ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv_toLinearMap]
  exact (ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv D n).surjective.comp (hsurj n).1

private def ThreefoldHomologyCuspFibre.heightParameter (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) : ℂ :=
  CuspUniformization.exponential
    (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)

private theorem
    ThreefoldHomologyCuspFibre.heightParameter_ne_zero (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) : heightParameter D h ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

private theorem ThreefoldHomologyCuspFibre.heightParameter_norm (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    ‖heightParameter D h‖ = Real.exp (-2 * Real.pi * (h : ℝ)) := by
  change
    ‖CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)‖ =
      _
  calc
    _ =
        Real.exp
          (Real.log
            ‖CuspUniformization.exponential
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))).symm
    _ = _ := by
      rw [CuspUniformization.log_norm_exponential, ThreefoldOverlapMappingTorus.Cusp.logPoint_im]

private def ThreefoldHomologyCuspFibre.fibreToFull (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(RealTorus₄, ThreefoldHomologyFinitenessCusp.FullSpace D) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
        C(CuspUniformization.PuncturedQuotient D.correction D.radius,
          ThreefoldHomologyFinitenessCusp.FullSpace D)).comp
    (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h)

private theorem
    ThreefoldHomologyCuspFibre.fibreToFull_projection (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (fibreToFull D h x) = heightParameter D h :=
  ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_base D h 0 x

private theorem ThreefoldHomologyCuspFibre.fibreToFull_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (x : RealPlane₄) :
    fibreToFull D h (standardLattice.mkQ x) =
      (CuspUniformization.puncturedCuspCover D.correction D.radius
          ⟨((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h : ℂ),
              D.periods.periodEquiv
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h) x),
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0
                h).property⟩).val :=
  congrArg Subtype.val (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured_realCoordinates D h x)

private def ThreefoldHomologyCuspFibre.fibreAtHeight (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(RealTorus₄,
      CuspControlledRetraction.ActualQuotientFibre D.correction D.radius (heightParameter D h))
    where
  toFun x := ⟨fibreToFull D h x, fibreToFull_projection D h x⟩
  continuous_toFun := (fibreToFull D h).continuous.subtype_mk _

private theorem
    ThreefoldHomologyCuspFibre.fibreToPunctured_product (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D
        (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h x) =
      (h,
        MappingTorus.HomologyCover.fibreInclusion ThreefoldOverlapMappingTorus.Cusp.monodromy
          x) :=
  (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).apply_symm_apply _

private theorem
    ThreefoldHomologyCuspFibre.fibreAtHeight_injective (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    Function.Injective (fibreAtHeight D h) := by
  intro x y hxy
  have hfull : fibreToFull D h x = fibreToFull D h y :=
    congrArg
      (fun q :
          CuspControlledRetraction.ActualQuotientFibre D.correction D.radius
            (heightParameter D h) =>
        q.val)
      hxy
  have hp :
    ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h x =
      ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h y :=
    Subtype.ext hfull
  have hm :=
    congrArg Prod.snd
      (congrArg (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D) hp)
  rw [fibreToPunctured_product, fibreToPunctured_product] at hm
  change
    MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (0, x) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (0, y) at hm
  obtain ⟨k, hk, he⟩ :=
    (MappingTorus.mk_eq_mk_iff ThreefoldOverlapMappingTorus.Cusp.monodromy _ _).mp hm
  have hk0 : k = 0 := by
    have hk' : (k : ℝ) = 0 := by
      change (0 : ℝ) = 0 + (k : ℝ) at hk
      linarith
    exact_mod_cast hk'
  subst k
  simpa using he.symm

private theorem
    ThreefoldHomologyCuspFibre.fibreAtHeight_surjective (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    Function.Surjective (fibreAtHeight D h) := by
  intro q
  let s := ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h
  have hs : ‖CuspUniformization.exponential (s : ℂ)‖ < D.radius :=
    (SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.property
  have hq :
    q.val ∈
      Set.range
        (CuspUniformization.fibreMap D.correction D.radius s hs (D.logarithmic_height s)
          (D.logarithmic_drift s)) := by
    rw [CuspUniformization.fibreMap_range]
    exact q.property
  obtain ⟨y, hy⟩ := hq
  obtain ⟨z, rfl⟩ :=
    (CuspUniformization.periodData D.correction s (D.logarithmic_height s)
          (D.logarithmic_drift s)).lattice.mkQ_surjective
      y
  refine ⟨standardLattice.mkQ ((D.periods.periodEquiv s).symm z), Subtype.ext ?_⟩
  change fibreToFull D h (standardLattice.mkQ ((D.periods.periodEquiv s).symm z)) = q.val
  rw [fibreToFull_realCoordinates]
  change
    CuspUniformization.fibreCover D.correction D.radius s hs
        (D.periods.periodEquiv s ((D.periods.periodEquiv s).symm z)) =
      q.val
  rw [LinearEquiv.apply_symm_apply]
  exact hy

private def ThreefoldHomologyCuspFibre.heightFibreHomeomorph (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    RealTorus₄ ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre D.correction D.radius (heightParameter D h) := by
  letI :=
    CuspQuotient.quotient_t2Space D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact
    Continuous.homeoOfEquivCompactToT2 (f :=
      Equiv.ofBijective (fibreAtHeight D h)
        ⟨fibreAtHeight_injective D h, fibreAtHeight_surjective D h⟩)
      (fibreAtHeight D h).continuous

private theorem ThreefoldHomologyCuspFibre.heightFibreHomeomorph_inclusion
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    (actualFibreInclusion D (heightParameter D h)).comp
        (heightFibreHomeomorph D h : C(RealTorus₄, _)) =
      fibreToFull D h :=
  rfl

private def ThreefoldHomologyCuspFibre.fibreHeightHomotopy (D : SpecialPeriods.CuspFamily.Data)
    (h₀ h₁ : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    (fibreToFull D h₀).Homotopy (fibreToFull D h₁)
    where
  toFun
    p :=
    ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
        (ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀ (p.1, h₁),
          MappingTorus.HomologyCover.fibreInclusion ThreefoldOverlapMappingTorus.Cusp.monodromy
            p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm.continuous.comp
        (((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).continuous.comp
              (continuous_fst.prodMk continuous_const)).prodMk
          ((MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy).continuous.comp
            continuous_snd)))
  map_zero_left
    x :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h,
              MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy x)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_zero_left h₁)
  map_one_left
    x :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h,
              MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy x)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_one_left h₁)

/-- Compatible local pieces and transition maps for gluing a threefold over a base. -/
public
structure ThreefoldGluing.Data (B : Type u) [TopologicalSpace B] where
  /-- The index type of the local pieces. -/
  J : Type u
  /-- The open base patch indexed by each local piece. -/
  patch : J → TopologicalSpace.Opens B
  cover : TopologicalSpace.IsOpenCover patch
  /-- The topological space lying over each base patch. -/
  piece : J → TopCat.{u}
  /-- The projection from each local piece to the base. -/
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  /-- The partial homeomorphism identifying a pair of local pieces. -/
  transition : ∀ i j, OpenPartialHomeomorph (piece i) (piece j)
  source_eq : ∀ i j, (transition i j).source = toBase i ⁻¹' (patch j : Set B)
  self_eq : ∀ i, transition i i = OpenPartialHomeomorph.refl (piece i)
  symm_eq : ∀ i j, (transition i j).symm = transition j i
  preserves_base : ∀ i j x, x ∈ (transition i j).source → toBase j (transition i j x) = toBase i x
  cocycle :
    ∀ i j k x,
      x ∈ (transition i j).source →
        transition i j x ∈ (transition j k).source →
          transition j k (transition i j x) = transition i k x

public
theorem ThreefoldGluing.Data.transition_map_source {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) : D.transition i j x ∈ (D.transition j i).source := by
  rw [← D.symm_eq i j]
  exact (D.transition i j).map_source hx

public
theorem ThreefoldGluing.Data.transition_inter {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j k : D.J) {x : D.piece i}
    (hx : x ∈ (D.transition i j).source) (hk : x ∈ (D.transition i k).source) :
    D.transition i j x ∈ (D.transition j k).source := by
  rw [D.source_eq] at hk ⊢
  change D.toBase j (D.transition i j x) ∈ D.patch k
  rw [D.preserves_base i j x hx]
  exact hk

/-- The core `TopCat` gluing datum associated to threefold gluing data. -/
public
abbrev ThreefoldGluing.Data.gluingCore {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : TopCat.GlueData.MkCore
    where
  J := D.J
  U := D.piece
  V i j := ⟨(D.transition i j).source, (D.transition i j).open_source⟩
  t i
    j :=
    TopCat.ofHom
      { toFun := fun x => ⟨D.transition i j x, D.transition_map_source i j x.property⟩
        continuous_toFun := (D.transition i j).continuousOn.domRestrict.subtype_mk _ }
  V_id i := by apply TopologicalSpace.Opens.ext; simp [D.self_eq]
  t_id
    i := by
    funext x
    exact
      Subtype.ext
        (congrArg (fun e : OpenPartialHomeomorph (D.piece i) (D.piece i) => e x.val)
          (D.self_eq i))
  t_inter := by
    intro i j k x hx
    exact D.transition_inter i j k x.property hx
  cocycle i j k x hx := D.cocycle i j k x x.property (D.transition_inter i j k x.property hx)

/-- The `TopCat` gluing datum associated to threefold gluing data. -/
public
abbrev ThreefoldGluing.Data.gluing {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : TopCat.GlueData :=
  TopCat.GlueData.mk' D.gluingCore

/-- The topological space obtained by gluing the local pieces. -/
public
abbrev ThreefoldGluing.Data.Space {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) :=
  D.gluing.toGlueData.glued

private def
    ThreefoldGluing.Data.inclusion {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (i : D.J) : D.piece i → D.Space :=
  D.gluing.toGlueData.ι i

private theorem ThreefoldGluing.Data.inclusion_openEmbedding {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : Topology.IsOpenEmbedding (D.inclusion i) :=
  D.gluing.ι_isOpenEmbedding i

private theorem ThreefoldGluing.Data.inclusion_jointly_surjective {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) : ∃ i z, D.inclusion i z = x :=
  D.gluing.ι_jointly_surjective x

private theorem ThreefoldGluing.Data.inclusion_eq_iff {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i j : D.J) (x : D.piece i) (y : D.piece j) :
    D.inclusion i x = D.inclusion j y ↔ x ∈ (D.transition i j).source ∧ D.transition i j x = y := by
  refine (D.gluing.ι_eq_iff_rel i j x y).trans ?_
  constructor
  · rintro ⟨⟨z, hz⟩, hzx, hzy⟩
    change z = x at hzx
    change D.transition i j z = y at hzy
    subst z
    exact ⟨hz, hzy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨x, hx⟩, rfl, hxy⟩

private def ThreefoldGluing.Data.representative {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) : Σ i, D.piece i :=
  ⟨(D.inclusion_jointly_surjective x).choose,
    (D.inclusion_jointly_surjective x).choose_spec.choose⟩

private theorem ThreefoldGluing.Data.inclusion_representative {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (x : D.Space) :
    D.inclusion (D.representative x).1 (D.representative x).2 = x :=
  (D.inclusion_jointly_surjective x).choose_spec.choose_spec

private def
    ThreefoldGluing.Data.projection {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (x : D.Space) : B :=
  D.toBase (D.representative x).1 (D.representative x).2

@[simp]
private theorem ThreefoldGluing.Data.projection_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (x : D.piece i) :
    D.projection (D.inclusion i x) = D.toBase i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change D.toBase r.1 r.2 = D.toBase i x
  rw [← h.2]
  exact (D.preserves_base r.1 i r.2 h.1).symm

private theorem ThreefoldGluing.Data.projection_continuous {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) : Continuous D.projection := by
  rw [continuous_def]
  intro U hU
  rw [D.gluing.isOpen_iff]
  change ∀ i : D.J, IsOpen (D.inclusion i ⁻¹' (D.projection ⁻¹' U))
  intro i
  convert hU.preimage (D.toBase i).continuous using 1
  ext x
  change D.projection (D.inclusion i x) ∈ U ↔ D.toBase i x ∈ U
  rw [D.projection_inclusion]

private theorem ThreefoldGluing.Data.inclusion_range {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    Set.range (D.inclusion i) = D.projection ⁻¹' (D.patch i : Set B) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change D.projection (D.inclusion i z) ∈ D.patch i
    rw [D.projection_inclusion]
    exact D.toBase_mem i z
  · intro hx
    obtain ⟨j, z, rfl⟩ := D.inclusion_jointly_surjective x
    have hz : z ∈ (D.transition j i).source := by
      rw [D.source_eq]
      simpa only [Set.mem_preimage, projection_inclusion] using hx
    exact ⟨D.transition j i z, ((D.inclusion_eq_iff j i z _).mpr ⟨hz, rfl⟩).symm⟩

private def ThreefoldGluing.Data.localProjection {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : C(D.piece i, D.patch i)
    where
  toFun x := ⟨D.toBase i x, D.toBase_mem i x⟩
  continuous_toFun := (D.toBase i).continuous.subtype_mk _

private def ThreefoldGluing.Data.patchHomeomorph {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    D.piece i ≃ₜ (D.projection ⁻¹' (D.patch i : Set B)) :=
  (D.inclusion_openEmbedding i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (D.inclusion_range i))

private theorem ThreefoldGluing.Data.patchHomeomorph_projection {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (x : D.piece i) :
    (D.patch i : Set B).restrictPreimage D.projection (D.patchHomeomorph i x) =
      D.localProjection i x := by
  apply Subtype.ext
  exact D.projection_inclusion i x

private instance ThreefoldGluing.Data.spaceT2 {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [T2Space B] [∀ i, T2Space (D.piece i)] : T2Space D.Space := by
  constructor
  intro x y hxy
  by_cases hb : D.projection x = D.projection y
  · obtain ⟨i, hi⟩ := D.cover.exists_mem (D.projection x)
    have hx : x ∈ Set.range (D.inclusion i) := by rw [D.inclusion_range]; exact hi
    have hy : y ∈ Set.range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection y ∈ D.patch i
      rw [← hb]
      exact hi
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (congrArg (D.inclusion i) h)
    obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation hab
    refine
      ⟨D.inclusion i '' U, D.inclusion i '' V, (D.inclusion_openEmbedding i).isOpenMap _ hU,
        (D.inclusion_openEmbedding i).isOpenMap _ hV, Set.mem_image_of_mem _ ha,
        Set.mem_image_of_mem _ hb, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb', hzb⟩
    have hab' := (D.inclusion_openEmbedding i).injective (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hUV) ha' (hab'.symm ▸ hb')
  · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hb
    exact
      ⟨D.projection ⁻¹' U, D.projection ⁻¹' V, hU.preimage D.projection_continuous,
        hV.preimage D.projection_continuous, hx, hy, hUV.preimage D.projection⟩

private def ThreefoldGluing.Data.parametrization {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) :
    OpenPartialHomeomorph (D.piece i) D.Space :=
  (D.inclusion_openEmbedding i).toOpenPartialHomeomorph (D.inclusion i)

@[simp]
private theorem ThreefoldGluing.Data.parametrization_target {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) :
    (D.parametrization i).target = Set.range (D.inclusion i) := by simp [parametrization]

private theorem ThreefoldGluing.Data.parametrization_transition {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i j : D.J) {x : D.piece i}
    (hx : D.inclusion i x ∈ Set.range (D.inclusion j)) :
    x ∈ (D.transition i j).source ∧
      (D.parametrization j).symm (D.inclusion i x) = D.transition i j x := by
  obtain ⟨y, hy⟩ := hx
  have he := (D.inclusion_eq_iff i j x y).mp hy.symm
  refine ⟨he.1, ?_⟩
  rw [← hy]
  exact ((D.inclusion_openEmbedding j).toOpenPartialHomeomorph_left_inv).trans he.2.symm

@[simp]
private theorem
    ThreefoldGluing.Data.parametrization_symm_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) (x : D.piece i) :
    (D.parametrization i).symm (D.inclusion i x) = x :=
  (D.parametrization i).left_inv (Set.mem_univ x)

private def
    ThreefoldGluing.Data.gluedChart {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    OpenPartialHomeomorph D.Space E :=
  (D.parametrization i).symm.trans (chartAt E x)

private theorem ThreefoldGluing.Data.gluedChart_symm {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    ((D.gluedChart i x).symm : E → D.Space) = D.inclusion i ∘ (chartAt E x).symm := by
  funext z
  rfl

@[simp]
private theorem ThreefoldGluing.Data.gluedChart_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x y : D.piece i) :
    D.gluedChart i x (D.inclusion i y) = chartAt E x y := by
  change chartAt E x ((D.parametrization i).symm (D.inclusion i y)) = _
  rw [parametrization_symm_inclusion]

private theorem
    ThreefoldGluing.Data.gluedChart_inclusion_mem_source {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    D.inclusion i x ∈ (D.gluedChart (E := E) i x).source := by
  change
    D.inclusion i x ∈ (D.parametrization i).target ∧
      (D.parametrization i).symm (D.inclusion i x) ∈ (chartAt E x).source
  rw [parametrization_target, parametrization_symm_inclusion]
  exact ⟨Set.mem_range_self x, mem_chart_source E x⟩

@[instance_reducible]
private def ThreefoldGluing.Data.chartedSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] : ChartedSpace E D.Space
    where
  atlas := Set.range (fun r : Σ i, D.piece i => D.gluedChart (E := E) r.1 r.2)
  chartAt x := D.gluedChart (D.representative x).1 (D.representative x).2
  mem_chart_source
    x := by
    simpa only [inclusion_representative] using
      D.gluedChart_inclusion_mem_source (E := E) (D.representative x).1 (D.representative x).2
  chart_mem_atlas x := Set.mem_range_self (D.representative x)

private theorem ThreefoldGluing.Data.gluedChart_mem_atlas {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    letI := D.chartedSpace (E := E)
    D.gluedChart i x ∈ atlas E D.Space :=
  Set.mem_range_self (⟨i, x⟩ : Σ i, D.piece i)

private theorem ThreefoldGluing.Data.gluedChart_transition_apply {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i j : D.J) (x : D.piece i) (y : D.piece j) {z : E}
    (hz : z ∈ ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source) :
    ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)) z =
      chartAt E y (D.transition i j ((chartAt E x).symm z)) := by
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈ (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ Set.range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  have he := (D.parametrization_transition i j hrange).2
  change chartAt E y ((D.parametrization j).symm (D.inclusion i ((chartAt E x).symm z))) = _
  rw [he]

private theorem ThreefoldGluing.Data.contMDiffOn_of_comp_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)] {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (f : D.Space → N) {U : Set D.Space}
    (hU : IsOpen U)
    (hf :
      ∀ i, ContMDiffOn (modelWithCornersSelf ℂ E) I ω (f ∘ D.inclusion i) (D.inclusion i ⁻¹' U)) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) I ω f U := by
  have hparam (i : D.J) (z : D.piece i) : D.parametrization i z = D.inclusion i z := rfl
  let := D.chartedSpace (E := E)
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (D.gluedChart (E := E) (D.representative x).1 (D.representative x).2).source :=
    mem_chart_source E x
  have hre :
    D.inclusion (D.representative x).1 ((D.parametrization (D.representative x).1).symm x) = x :=
    (D.parametrization (D.representative x).1).right_inv hx.1
  have hpre :
    (D.parametrization (D.representative x).1).symm x ∈
      D.inclusion (D.representative x).1 ⁻¹' U := by
    change D.inclusion _ _ ∈ U
    rwa [hre]
  have hlocal :=
    (hf (D.representative x).1).contMDiffAt
      ((hU.preimage (D.inclusion_openEmbedding _).continuous).mem_nhds hpre)
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp
      hlocal
  have hchart : chartAt E x = D.gluedChart (D.representative x).1 (D.representative x).2 := rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, gluedChart,
    Function.comp_def] using hsrc

private theorem
    ThreefoldGluing.Data.gluedChart_transition_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i j : D.J) (x : D.piece i) (y : D.piece j) :
    ContDiffOn ℂ ω ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y))
      ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E x).target := hz.1.1
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈ (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ Set.range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  obtain ⟨htr, he⟩ := D.parametrization_transition i j hrange
  have ha := (chartAt E x).map_target hza
  have hb : D.transition i j ((chartAt E x).symm z) ∈ (chartAt E y).source := by
    rw [← he]
    exact hinc.2
  have hmid := (hhol i j).contMDiffAt ((D.transition i j).open_source.mem_nhds htr)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' : ContDiffAt ℂ ω (chartAt E y ∘ D.transition i j ∘ (chartAt E x).symm) z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E x).right_inv hza] using hc
  apply hc'.contDiffWithinAt.congr_of_mem ?_ hz
  intro w hw
  exact D.gluedChart_transition_apply i j x y hw

private theorem ThreefoldGluing.Data.isManifold {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source) :
    letI := D.chartedSpace (E := E)
    IsManifold (modelWithCornersSelf ℂ E) ω D.Space := by
  let := D.chartedSpace (E := E)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨⟨i, x⟩, rfl⟩ ⟨⟨j, y⟩, rfl⟩
  simpa using D.gluedChart_transition_holomorphic hhol i j x y

private theorem ThreefoldGluing.Data.inclusion_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.inclusion i) := by
  let := D.chartedSpace (E := E)
  let := D.isManifold hhol
  intro x
  have he :=
    IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := ω)
      (D.gluedChart_mem_atlas i x)
  have ht : chartAt E x x ∈ (D.gluedChart (E := E) i x).target := by
    simpa only [gluedChart_inclusion] using
      (D.gluedChart (E := E) i x).map_source (D.gluedChart_inclusion_mem_source i x)
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas he ht
  have hc : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (chartAt E x) x :=
    contMDiffOn_chart.contMDiffAt ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  apply (hsymm.comp x hc).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  change D.inclusion i y = (D.gluedChart (E := E) i x).symm (chartAt E x y)
  rw [gluedChart_symm, Function.comp_apply, (chartAt E x).left_inv hy]

private theorem
    ThreefoldGluing.Data.parametrization_symm_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.parametrization i).symm
      (D.parametrization i).target := by
  let := D.chartedSpace (E := E)
  rw [parametrization_target]
  apply
    D.contMDiffOn_of_comp_inclusion (modelWithCornersSelf ℂ E) (D.parametrization i).symm
      (D.inclusion_openEmbedding i).isOpen_range
  intro j
  exact
    ((hhol j i).mono (fun x hx => (D.parametrization_transition j i hx).1)).congr
      (fun x hx => (D.parametrization_transition j i hx).2)

end Mathoverflow1973

end
