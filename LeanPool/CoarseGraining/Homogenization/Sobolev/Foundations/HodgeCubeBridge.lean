/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalTranslation

/-! # Hodge Cube Bridge -/

@[expose] public section

namespace Homogenization

/-!
This file transports the open-cube Hodge converse to the half-open centered
cube used by the deterministic multiscale layer.
-/

theorem memVectorL2_comp_addRight_of_memVectorL2_translateSet
    {d : ℕ} {U : Set (Vec d)} {z : Vec d} {f : Vec d → Vec d}
    (hf : MemVectorL2 (translateSet z U) f) :
    MemVectorL2 U (fun x => f (x + z)) := by
  simpa [MemVectorL2, volumeMeasureOn, Function.comp] using!
    hf.comp_measurePreserving (measurePreserving_addRight_restrict_translateSet (d := d) z U)

theorem memVectorL2_translateSet_of_memVectorL2
    {d : ℕ} {U : Set (Vec d)} {z : Vec d} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    MemVectorL2 (translateSet z U) (fun x => f (x - z)) := by
  simpa [MemVectorL2, volumeMeasureOn, Function.comp] using!
    hf.comp_measurePreserving (measurePreserving_subRight_restrict_translateSet (d := d) z U)

/-- The Hodge converse is invariant under translating the domain. -/
theorem hodgeConverseCriterion_translateSet
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (z : Vec d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (translateSet z U))]
    (hHodge : HodgeConverseCriterion U) :
    HodgeConverseCriterion (translateSet z U) := by
  intro f hf horth
  let f0 : Vec d → Vec d := fun x => f (x + z)
  have hf0 : MemVectorL2 U f0 :=
    memVectorL2_comp_addRight_of_memVectorL2_translateSet (U := U) (z := z) hf
  have horth0 :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f0 x) ∂MeasureTheory.volume = 0 := by
    intro g hg hsol
    have hgTranslate :
        MemVectorL2 (translateSet z U) (fun x => g (x - z)) :=
      memVectorL2_translateSet_of_memVectorL2 (U := U) (z := z) hg
    have hsolTranslate :
        IsSolenoidalZeroNormalTraceOn (translateSet z U) (fun x => g (x - z)) :=
      isSolenoidalZeroNormalTraceOn_translateSet hsol z
    have htranslated :
        ∫ x in translateSet z U, vecDot (g (x - z)) (f x) ∂MeasureTheory.volume = 0 :=
      horth hgTranslate hsolTranslate
    have hchange :
        ∫ x in U, vecDot (g x) (f0 x) ∂MeasureTheory.volume =
          ∫ x in translateSet z U, vecDot (g (x - z)) (f x) ∂MeasureTheory.volume := by
      simpa [f0, sub_eq_add_neg, add_assoc] using
        (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
          (fun x => vecDot (g (x - z)) (f x)))
    exact hchange.trans htranslated
  have hpot0 : IsPotentialOn U f0 := hHodge hf0 horth0
  have hpotTranslate :
      IsPotentialOn (translateSet z U) (fun x => f0 (x - z)) :=
    isPotentialOn_translateSet hpot0 z
  simpa [f0, sub_eq_add_neg, add_assoc] using hpotTranslate

/--
The half-open centered cube satisfies the Hodge converse because it agrees
almost everywhere with the corresponding open centered cube, and the latter is a
bounded open convex domain.
-/
theorem hodgeConverseCriterion_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet (originCube d n)))] :
    HodgeConverseCriterion (cubeSet (originCube d n)) := by
  have hfiniteOpen :
      MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) :=
    hfiniteOpen
  intro f hf horth
  have hfOpen : MemVectorL2 (openCubeSet (originCube d n)) f := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube] using hf
  have horthOpen :
      ∀ {g : Vec d → Vec d}, MemVectorL2 (openCubeSet (originCube d n)) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g →
          ∫ x in openCubeSet (originCube d n), vecDot (g x) (f x) ∂MeasureTheory.volume = 0 := by
    intro g hg hsol
    have hgCube : MemVectorL2 (cubeSet (originCube d n)) g := by
      simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube] using hg
    have hsolCube :
        IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n)) g :=
      isSolenoidalZeroNormalTraceOn_cubeSet_originCube_of_openCubeSet hsol
    have hcube :
        ∫ x in cubeSet (originCube d n), vecDot (g x) (f x) ∂MeasureTheory.volume = 0 :=
      horth hgCube hsolCube
    have hset :
        ∫ x in cubeSet (originCube d n), vecDot (g x) (f x) ∂MeasureTheory.volume =
          ∫ x in openCubeSet (originCube d n), vecDot (g x) (f x) ∂MeasureTheory.volume :=
      setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
    rwa [hset] at hcube
  have hopen :
      IsPotentialOn (openCubeSet (originCube d n)) f :=
    hodgeConverseCriterion_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n))
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hfOpen horthOpen
  exact isPotentialOn_cubeSet_originCube_of_openCubeSet hopen

/-- Packaged centered half-open cube Hodge converse. -/
theorem hasHodgeConverse_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet (originCube d n)))] :
    HasHodgeConverse (cubeSet (originCube d n)) :=
  hasHodgeConverse_of_orthogonal_criterion
    (hodgeConverseCriterion_cubeSet_originCube (d := d) (n := n))

private theorem cubeSet_eq_translateSet_originCube_for_hodge {d : ℕ}
    (Q : TriadicCube d) :
    cubeSet Q =
      translateSet (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
        (cubeSet (originCube d Q.scale)) := by
  cases Q with
  | mk scale index =>
      apply Set.ext
      intro x
      rw [mem_translateSet_iff_sub_mem]
      constructor
      · intro hx i
        simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i
      · intro hx i
        simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i

/-- Every half-open triadic cube satisfies the Hodge converse. -/
theorem hodgeConverseCriterion_cubeSet_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))] :
    HodgeConverseCriterion (cubeSet Q) := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  let U0 : Set (Vec d) := cubeSet (originCube d Q.scale)
  have hcube : cubeSet Q = translateSet z U0 := by
    simpa [z, U0] using cubeSet_eq_translateSet_originCube_for_hodge Q
  have hfiniteOrigin :
      MeasureTheory.IsFiniteMeasure (volumeMeasureOn U0) := by
    let : Fact (MeasureTheory.volume U0 < ⊤) := by
      refine ⟨?_⟩
      simpa [U0] using volume_cubeSet_lt_top (originCube d Q.scale)
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U0)
    infer_instance
  have hfiniteTranslate :
      MeasureTheory.IsFiniteMeasure (volumeMeasureOn (translateSet z U0)) := by
    simpa [hcube] using
      (inferInstance : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)))
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U0) := hfiniteOrigin
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (translateSet z U0)) := hfiniteTranslate
  have horigin : HodgeConverseCriterion U0 := by
    change HodgeConverseCriterion (cubeSet (originCube d Q.scale))
    exact hodgeConverseCriterion_cubeSet_originCube (d := d) (n := Q.scale)
  have htranslated : HodgeConverseCriterion (translateSet z U0) := by
    exact hodgeConverseCriterion_translateSet (U := U0) z horigin
  intro f hf horth
  have hfTranslate : MemVectorL2 (translateSet z U0) f := by
    simpa [← hcube] using hf
  have horthTranslate :
      ∀ {g : Vec d → Vec d}, MemVectorL2 (translateSet z U0) g →
        IsSolenoidalZeroNormalTraceOn (translateSet z U0) g →
          ∫ x in translateSet z U0, vecDot (g x) (f x) ∂MeasureTheory.volume = 0 := by
    intro g hg hsol
    have hgCube : MemVectorL2 (cubeSet Q) g := by
      simpa [hcube] using hg
    have hsolCube : IsSolenoidalZeroNormalTraceOn (cubeSet Q) g := by
      simpa [hcube] using hsol
    have hcubeOrth :
        ∫ x in cubeSet Q, vecDot (g x) (f x) ∂MeasureTheory.volume = 0 :=
      horth hgCube hsolCube
    simpa [hcube] using hcubeOrth
  have hpotTranslate : IsPotentialOn (translateSet z U0) f :=
    htranslated hfTranslate horthTranslate
  simpa [← hcube] using hpotTranslate

/-- Packaged Hodge converse on every half-open triadic cube. -/
theorem hasHodgeConverse_cubeSet_triadicCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))] :
    HasHodgeConverse (cubeSet Q) :=
  hasHodgeConverse_of_orthogonal_criterion
    (hodgeConverseCriterion_cubeSet_triadicCube Q)

instance instHasHodgeConverseCubeSet
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))] :
    HasHodgeConverse (cubeSet Q) :=
  hasHodgeConverse_cubeSet_triadicCube Q

end Homogenization
