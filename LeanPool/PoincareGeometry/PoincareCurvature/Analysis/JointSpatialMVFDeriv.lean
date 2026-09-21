/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.JointSpatialDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart

/-!
# Joint regularity of a manifold spatial derivative

This module transfers the fixed-coordinate spatial-derivative lemma to a
manifold chart.  The local-frame direction is pulled back through the chart,
so that the result can be used for scalar fields such as the terms occurring
in the explicit DeTurck correction.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A local tangent frame, pulled back through a fixed extended chart, is
`C¹` on the part of the chart where the frame is defined. -/
theorem contDiffOn_localFrameInChart_one
    [I.Boundaryless]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i : ι) :
    ContDiffOn ℝ 1 (CovariantDerivative.localFrameInChart (I := I) p e b i)
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet) := by
  letI selfTangentNormedAddCommGroup (z : E) :
      NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ E) z) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI selfTangentNormedSpace (z : E) :
      NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ E) z) :=
    inferInstanceAs (NormedSpace ℝ E)
  let s := (extChartAt I p).target
  let t := e.baseSet
  have hV : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) 1
      (T% (e.localFrame b i)) t :=
    e.contMDiffOn_localFrame_baseSet (I := I)
      (n := (1 : WithTop ℕ∞)) b i
  have hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 2
      (extChartAt I p).symm s := contMDiffOn_extChartAt_symm p
  have hf' : ∀ z ∈ s ∩ (extChartAt I p).symm ⁻¹' t,
      (mfderiv[s] (extChartAt I p).symm z).IsInvertible := by
    intro z hz
    have hrange : Set.range I ∈ nhds z :=
      mem_of_superset ((isOpen_extChartAt_target p).mem_nhds hz.1)
        (extChartAt_target_subset_range p)
    have hsnhds : s ∈ nhds z := (isOpen_extChartAt_target p).mem_nhds hz.1
    simpa [mfderivWithin_of_mem_nhds hsnhds,
      mfderivWithin_of_mem_nhds hrange] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := I) hz.1)
  have hpull : ContMDiffOn (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E).tangent 1
      (T% (VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (e.localFrame b i) s))
      (s ∩ (extChartAt I p).symm ⁻¹' t) :=
    hV.mpullbackWithin_vectorField_inter hf hf'
      (isOpen_extChartAt_target p).uniqueMDiffOn (by norm_num)
  have hpair :=
    (contMDiff_tangentBundleModelSpaceHomeomorph
      (I := modelWithCornersSelf ℝ E) (n := (1 : WithTop ℕ∞))).comp_contMDiffOn hpull
  rw [← modelWithCornersSelf_prod, contMDiffOn_iff_contDiffOn] at hpair
  have hpullModel := contDiffOn_snd.comp hpair (fun _ _ => Set.mem_univ _)
  have hpullModel' : ContDiffOn ℝ 1
      (VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (e.localFrame b i) s)
      (s ∩ (extChartAt I p).symm ⁻¹' t) := by
    convert hpullModel using 1 <;> rfl
  refine hpullModel'.congr fun z hz => ?_
  unfold CovariantDerivative.localFrameInChart VectorField.mpullbackWithin
  have hsnhds : s ∈ nhds z := (isOpen_extChartAt_target p).mem_nhds hz.1
  have hrange : Set.range I ∈ nhds z :=
    mem_of_superset hsnhds (extChartAt_target_subset_range p)
  rw [mfderivWithin_of_mem_nhds hsnhds,
    mfderivWithin_of_mem_nhds hrange]

/-- Coordinate form of the pointwise joint-regularity statement for a
manifold spatial derivative.  The vector field is represented in the fixed
tangent trivialization at the base point, which is the representation used by
`ContMDiffAt.mfderiv_apply`. -/
theorem contMDiffAt_mvfderiv_apply_coordinate_of_joint
    {F : ℝ → M → ℝ} {X : ∀ x : M, TM x} {r : ℝ × M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 2
      (fun q : ℝ × M => F q.1 q.2) r)
    (hX : ContMDiffAt I (I.prod (𝓘(ℝ, E))) 1
      (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) r.2) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 1
      (fun q : ℝ × M =>
        (inTangentCoordinates I (𝓘(ℝ, ℝ))
          (fun z : ℝ × M => z.2)
          (fun z : ℝ × M => F z.1 z.2)
          (fun z : ℝ × M =>
            mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F z.1 y) z.2)
          r q)
          ((trivializationAt E TM r.2
            (⟨q.2, X q.2⟩ : TangentBundle I M)).2)) r := by
  let s : ℝ × M → TangentBundle I M :=
    fun q => ⟨q.2, X q.2⟩
  let e := trivializationAt E TM r.2
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod (𝓘(ℝ, E))) 1 s r :=
    hX.comp r contMDiffAt_snd
  have hsource : s r ∈ e.source := by
    rw [TangentBundle.trivializationAt_source]
    exact mem_chart_source _ _
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, E)) 1
      (fun q : ℝ × M => (e (s q)).2) r :=
    ((e.contMDiffAt_iff hsource).mp hs).2
  let f : (ℝ × M) → M → ℝ := fun q y => F q.1 y
  let g : (ℝ × M) → M := fun q => q.2
  let g₁ : (ℝ × M) → (ℝ × M) := id
  let g₂ : (ℝ × M) → E := fun q => (e (s q)).2
  have hproj : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod I)
      (𝓘(ℝ, ℝ).prod I) 2
      (fun q : (ℝ × M) × M => (q.1.1, q.2)) (r, g r) := by
    exact (contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd
  have hf : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ)) 2
      (Function.uncurry f) (g₁ r, g (g₁ r)) := by
    convert hF.comp (r, g r) hproj using 1 <;> rfl
  have hderiv := ContMDiffAt.mfderiv_apply
    (I := I) (I' := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ).prod I)
    (J' := 𝓘(ℝ, ℝ).prod I)
    (f := f) (g := g) (g₁ := g₁) (g₂ := g₂)
    hf contMDiffAt_snd contMDiffAt_id hcoord (by norm_num)
  simpa [f, g, g₁, g₂, s, e] using hderiv

/-- The coordinate expression produced by
`contMDiffAt_mvfderiv_apply_coordinate_of_joint` is the intrinsic directional
derivative when written along the inverse of its fixed tangent chart. -/
theorem inTangentCoordinates_mvfderiv_apply_coordinate_eq_on_chart
    {F : ℝ → M → ℝ} {X : ∀ x : M, TM x}
    {r : ℝ × M} {t : ℝ} {z : E}
    (hz : z ∈ (extChartAt I r.2).target) :
    (inTangentCoordinates I (𝓘(ℝ, ℝ))
      (fun w : ℝ × M => w.2)
      (fun w : ℝ × M => F w.1 w.2)
      (fun w : ℝ × M =>
        mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F w.1 y) w.2)
      r (t, (extChartAt I r.2).symm z))
      ((trivializationAt E TM r.2
        (⟨(extChartAt I r.2).symm z,
          X ((extChartAt I r.2).symm z)⟩ : TangentBundle I M)).2) =
      mvfderiv (I := I) (fun y : M => F t y)
        ((extChartAt I r.2).symm z) (X ((extChartAt I r.2).symm z)) := by
  let e := trivializationAt E TM r.2
  let e' := trivializationAt ℝ (TangentSpace (𝓘(ℝ, ℝ)) : ℝ → Type _) (F r.1 r.2)
  have hsrc : (extChartAt I r.2).symm z ∈ (chartAt H r.2).source := by
    simpa only [extChartAt_source] using (extChartAt I r.2).map_target hz
  have hebase : (extChartAt I r.2).symm z ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hsrc
  have houtbase : F t ((extChartAt I r.2).symm z) ∈ e'.baseSet := by
    simp [e', TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
  have hinput :
      (e.continuousLinearEquivAt ℝ ((extChartAt I r.2).symm z) hebase).symm
        (e (⟨(extChartAt I r.2).symm z,
          X ((extChartAt I r.2).symm z)⟩ : TangentBundle I M)).2 =
        X ((extChartAt I r.2).symm z) := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hebase]
    rw [← Trivialization.coe_continuousLinearEquivAt_eq' e hebase]
    exact (e.continuousLinearEquivAt ℝ ((extChartAt I r.2).symm z) hebase).symm_apply_apply _
  have hout :
      (e'.continuousLinearEquivAt ℝ (F t ((extChartAt I r.2).symm z)) houtbase)
        ((mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F t y)
          ((extChartAt I r.2).symm z)) (X ((extChartAt I r.2).symm z))) =
        mvfderiv (I := I) (fun y : M => F t y)
          ((extChartAt I r.2).symm z) (X ((extChartAt I r.2).symm z)) := by
    rw [mvfderiv]
    change
      (↑(e'.continuousLinearEquivAt ℝ (F t ((extChartAt I r.2).symm z)) houtbase) :
        TangentSpace (𝓘(ℝ, ℝ)) (F t ((extChartAt I r.2).symm z)) →L[ℝ] ℝ)
        ((mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F t y)
          ((extChartAt I r.2).symm z)) (X ((extChartAt I r.2).symm z))) =
      (NormedSpace.fromTangentSpace (F t ((extChartAt I r.2).symm z)))
        ((mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F t y)
          ((extChartAt I r.2).symm z)) (X ((extChartAt I r.2).symm z)))
    rw [Trivialization.coe_continuousLinearEquivAt_eq' e' houtbase]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt]
    · simp [e', extChartAt_self_eq, modelWithCornersSelf_coe]
      rw [chartAt_self_eq]
      change fderiv ℝ (id : ℝ → ℝ) _ _ = _
      rw [fderiv_id]
      rfl
    · simpa [chartAt_self_eq]
  calc
    (inTangentCoordinates I (𝓘(ℝ, ℝ))
        (fun w : ℝ × M => w.2)
        (fun w : ℝ × M => F w.1 w.2)
        (fun w : ℝ × M =>
          mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F w.1 y) w.2)
        r (t, (extChartAt I r.2).symm z))
        ((trivializationAt E TM r.2
          (⟨(extChartAt I r.2).symm z,
            X ((extChartAt I r.2).symm z)⟩ : TangentBundle I M)).2) =
      (e'.continuousLinearEquivAt ℝ (F t ((extChartAt I r.2).symm z)) houtbase)
        ((mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F t y)
          ((extChartAt I r.2).symm z))
          ((e.continuousLinearEquivAt ℝ ((extChartAt I r.2).symm z) hebase).symm
            (e (⟨(extChartAt I r.2).symm z,
              X ((extChartAt I r.2).symm z)⟩ : TangentBundle I M)).2)) := by
        unfold inTangentCoordinates
        rw [ContinuousLinearMap.inCoordinates_eq hebase houtbase]
        rfl
    _ = (e'.continuousLinearEquivAt ℝ (F t ((extChartAt I r.2).symm z)) houtbase)
        ((mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F t y)
          ((extChartAt I r.2).symm z)) (X ((extChartAt I r.2).symm z))) := by
        rw [hinput]
    _ = _ := hout

/-- A jointly `C²` scalar field has a jointly `C¹` intrinsic spatial
derivative along any `C¹` tangent section. -/
theorem contMDiffAt_mvfderiv_apply_of_joint
    {F : ℝ → M → ℝ} {X : ∀ x : M, TM x} {r : ℝ × M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 2
      (fun q : ℝ × M => F q.1 q.2) r)
    (hX : ContMDiffAt I (I.prod (𝓘(ℝ, E))) 1
      (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) r.2) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 1
      (fun q : ℝ × M =>
        mvfderiv (I := I) (fun y : M => F q.1 y) q.2 (X q.2)) r := by
  let C : ℝ × M → ℝ := fun q =>
    (inTangentCoordinates I (𝓘(ℝ, ℝ))
      (fun z : ℝ × M => z.2)
      (fun z : ℝ × M => F z.1 z.2)
      (fun z : ℝ × M =>
        mfderiv (I := I) (I' := 𝓘(ℝ, ℝ)) (fun y : M => F z.1 y) z.2)
      r q)
      ((trivializationAt E TM r.2
        (⟨q.2, X q.2⟩ : TangentBundle I M)).2)
  have hC : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 1 C r := by
    simpa [C] using
      contMDiffAt_mvfderiv_apply_coordinate_of_joint (I := I) hF hX
  have hsourceN : (extChartAt I r.2).source ∈ 𝓝 r.2 := by
    rw [extChartAt_source]
    exact (chartAt H r.2).open_source.mem_nhds (mem_chart_source H r.2)
  have hnear : ∀ᶠ q : ℝ × M in 𝓝 r,
      q.2 ∈ (extChartAt I r.2).source :=
    continuousAt_snd.preimage_mem_nhds hsourceN
  refine hC.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with q hq
  have hformula :=
    inTangentCoordinates_mvfderiv_apply_coordinate_eq_on_chart
      (I := I) (F := F) (X := X) (r := r) (t := q.1)
      (z := (extChartAt I r.2) q.2)
      ((extChartAt I r.2).map_source hq)
  have hleft : (extChartAt I r.2).symm ((extChartAt I r.2) q.2) = q.2 :=
    (extChartAt I r.2).left_inv hq
  let G : M → ℝ := fun x =>
    mvfderiv (I := I) (fun y : M => F q.1 y) x (X x)
  have hqpair :
      (q.1, (extChartAt I r.2).symm ((extChartAt I r.2) q.2)) = q :=
    Prod.ext rfl hleft
  change G q.2 = C q
  calc
    G q.2 = G ((extChartAt I r.2).symm ((extChartAt I r.2) q.2)) :=
      congrArg G hleft.symm
    _ = C (q.1, (extChartAt I r.2).symm ((extChartAt I r.2) q.2)) := by
      exact hformula.symm
    _ = C q := by rw [hqpair]

/-- The local-frame instance of
`contMDiffAt_mvfderiv_apply_of_joint`.  This discharges the tangent-section
regularity input from the smoothness of a local frame. -/
theorem contMDiffAt_mvfderiv_apply_localFrame_of_joint
    {ι : Type*} (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (i : ι)
    {F : ℝ → M → ℝ} {r : ℝ × M} (hr : r.2 ∈ e.baseSet)
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 2
      (fun q : ℝ × M => F q.1 q.2) r) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 1
      (fun q : ℝ × M =>
        mvfderiv (I := I) (fun y : M => F q.1 y) q.2
          (e.localFrame b i q.2)) r := by
  apply contMDiffAt_mvfderiv_apply_of_joint (I := I) hF
  exact
    ((e.contMDiffOn_localFrame_baseSet (I := I)
      (n := (1 : WithTop ℕ∞)) b i) r.2 hr).contMDiffAt
      (e.open_baseSet.mem_nhds hr)

/-- On a local-frame domain, a jointly `C²` scalar field has a jointly `C¹`
intrinsic spatial derivative along each frame vector. -/
theorem contMDiffOn_mvfderiv_apply_localFrame_of_joint
    {ι : Type*} (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (i : ι)
    {F : ℝ → M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 2
      (fun q : ℝ × M => F q.1 q.2) (Set.univ ×ˢ e.baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ)) 1
      (fun q : ℝ × M =>
        mvfderiv (I := I) (fun y : M => F q.1 y) q.2
          (e.localFrame b i q.2)) (Set.univ ×ˢ e.baseSet) := by
  intro r hr
  have hopen : Set.univ ×ˢ e.baseSet ∈ 𝓝 r :=
    (isOpen_univ.prod e.open_baseSet).mem_nhds hr
  exact
    (contMDiffAt_mvfderiv_apply_localFrame_of_joint (I := I) e b i hr.2
      ((hF r hr).contMDiffAt hopen)).contMDiffWithinAt

end PoincareCurvature
