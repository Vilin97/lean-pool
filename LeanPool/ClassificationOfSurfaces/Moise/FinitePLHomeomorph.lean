/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.CommonSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension

/-!
# Finite PL homeomorphisms on compact plane polyhedra

This is the concrete PL category needed by Moise Chapters 5 and 6.  A witness records a pure
finite source complex on which an ambient homeomorphism is affine facewise.  Common subdivision
and pullback make these witnesses closed under symmetry and composition.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An ambient homeomorphism is finitely PL on `A`, with an explicit pure source complex. -/
structure FinitePLHomeomorphOn (h : Plane ≃ₜ Plane) (A : Set Plane) where
  /-- The `complex` declaration. -/
  complex : PlaneComplex
  support_eq : complex.support = A
  pure : complex.IsPure2
  affineOn : ∀ s ∈ complex.simplexes, IsAffineOn h (complex.cellCarrier s)

/-- A finite PL homeomorphism between two compact plane polyhedra.

The underlying function need not be meaningful, continuous, or injective away from `A`; all
geometric data is deliberately relative to the source support. -/
structure FinitePLHomeomorphBetween (f : Plane → Plane) (A B : Set Plane) where
  /-- The `complex` declaration. -/
  complex : PlaneComplex
  support_eq : complex.support = A
  pure : complex.IsPure2
  vertex_mem_support : ∀ v : complex.Vertex, complex.position v ∈ complex.support
  affineOn : ∀ s ∈ complex.simplexes, IsAffineOn f (complex.cellCarrier s)
  injOn : Set.InjOn f A
  image_eq : f '' A = B

namespace FinitePLHomeomorphBetween

variable {f g : Plane → Plane} {A B C : Set Plane}

/-- Forget the explicit pure witness. -/
theorem isPLOnSet (F : FinitePLHomeomorphBetween f A B) : IsPLOnSet A f := by
  exact ⟨F.complex, F.support_eq, F.complex, PlaneComplex.Subdivides.refl F.complex,
    F.affineOn⟩

theorem continuousOn (F : FinitePLHomeomorphBetween f A B) : ContinuousOn f A := by
  rw [← F.support_eq]
  exact (show IsPLOn F.complex f from
    ⟨F.complex, PlaneComplex.Subdivides.refl F.complex, F.affineOn⟩).continuousOn

/-- Reindex the certified target along a set equality. -/
def congrTarget (F : FinitePLHomeomorphBetween f A B) {C : Set Plane} (hBC : B = C) :
    FinitePLHomeomorphBetween f A C where
  complex := F.complex
  support_eq := F.support_eq
  pure := F.pure
  vertex_mem_support := F.vertex_mem_support
  affineOn := F.affineOn
  injOn := F.injOn
  image_eq := F.image_eq.trans hBC

/-- The target complex obtained by mapping every source face. -/
noncomputable def targetComplex (F : FinitePLHomeomorphBetween f A B) : PlaneComplex :=
  F.complex.mapComplexOn f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn

theorem targetComplex_support (F : FinitePLHomeomorphBetween f A B) :
    F.targetComplex.support = B := by
  rw [targetComplex, F.complex.mapComplexOn_support f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn, F.support_eq, F.image_eq]

theorem targetComplex_pure (F : FinitePLHomeomorphBetween f A B) :
    F.targetComplex.IsPure2 :=
  PlaneComplex.IsPure2.mapComplexOn F.complex F.pure f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn

theorem targetComplex_vertex_mem_support (F : FinitePLHomeomorphBetween f A B)
    (v : F.targetComplex.Vertex) :
    F.targetComplex.position v ∈ F.targetComplex.support := by
  rw [F.targetComplex_support]
  change f (F.complex.position v) ∈ B
  apply (Set.ext_iff.mp F.image_eq (f (F.complex.position v))).mp
  exact ⟨F.complex.position v,
    (Set.ext_iff.mp F.support_eq (F.complex.position v)).mp
      (F.vertex_mem_support v), rfl⟩

/-- A set-theoretic inverse, used only on the certified target polyhedron. -/
noncomputable def inverseOn (F : FinitePLHomeomorphBetween f A B) : Plane → Plane :=
  by
    classical
    exact fun y => if hy : y ∈ B then
      Classical.choose (show ∃ x ∈ A, f x = y by
        rw [← F.image_eq] at hy
        exact hy)
    else 0

theorem inverseOn_mem (F : FinitePLHomeomorphBetween f A B) {y : Plane} (hy : y ∈ B) :
    F.inverseOn y ∈ A := by
  simp only [inverseOn, dite_eq_left hy]
  exact (Classical.choose_spec (show ∃ x ∈ A, f x = y by
    rw [← F.image_eq] at hy
    exact hy)).1

theorem apply_inverseOn (F : FinitePLHomeomorphBetween f A B) {y : Plane} (hy : y ∈ B) :
    f (F.inverseOn y) = y := by
  simp only [inverseOn, dite_eq_left hy]
  exact (Classical.choose_spec (show ∃ x ∈ A, f x = y by
    rw [← F.image_eq] at hy
    exact hy)).2

theorem inverseOn_apply (F : FinitePLHomeomorphBetween f A B) {x : Plane} (hx : x ∈ A) :
    F.inverseOn (f x) = x := by
  have hfx : f x ∈ B := by
    rw [← F.image_eq]
    exact ⟨x, hx, rfl⟩
  apply F.injOn (F.inverseOn_mem hfx) hx
  rw [F.apply_inverseOn hfx]

theorem inverseOn_injOn (F : FinitePLHomeomorphBetween f A B) :
    Set.InjOn F.inverseOn B := by
  intro x hx y hy hxy
  calc
    x = f (F.inverseOn x) := (F.apply_inverseOn hx).symm
    _ = f (F.inverseOn y) := congrArg f hxy
    _ = y := F.apply_inverseOn hy

/-- On a subdivision of the target complex, the certified inverse is affine facewise. -/
theorem inverseOn_affineOn_of_subdivides_targetComplex
    (F : FinitePLHomeomorphBetween f A B) {R : PlaneComplex}
    (hR : R.Subdivides F.targetComplex) :
    ∀ s ∈ R.simplexes, IsAffineOn F.inverseOn (R.cellCarrier s) := by
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hR.2 s hs
  obtain ⟨t, ht, hut, htcard⟩ := F.pure u hu
  have hutCarrier : F.targetComplex.cellCarrier u ⊆
      F.targetComplex.cellCarrier t := convexHull_mono (Set.image_mono hut)
  have hinjSupport : Set.InjOn f F.complex.support := by
    simpa only [F.support_eq] using F.injOn
  have hsTarget : R.cellCarrier s ⊆ f '' F.complex.cellCarrier t := by
    exact hsu.trans (hutCarrier.trans_eq
      (F.complex.mapComplexOn_cellCarrier f F.vertex_mem_support hinjSupport
        F.affineOn ht))
  obtain ⟨a, hfa⟩ := F.affineOn t ht
  have hinterior : (interior (F.complex.cellCarrier t)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have hrange : Set.range (fun v : t => F.complex.position v) =
        F.complex.position '' (t : Set F.complex.Vertex) := by
      ext x
      simp
    rw [← hrange]
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exact ((F.complex.affineIndependent t ht).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
      (by simp [htcard, Plane])
  have haInjOn : Set.InjOn a (F.complex.cellCarrier t) := by
    intro x hx y hy hxy
    apply F.injOn
    · rw [← F.support_eq]
      exact F.complex.cellCarrier_subset_support ht hx
    · rw [← F.support_eq]
      exact F.complex.cellCarrier_subset_support ht hy
    · rw [hfa hx, hfa hy]
      exact hxy
  have haInj : Function.Injective a :=
    affineMap_injective_of_injOn_of_interior_nonempty a hinterior haInjOn
  have haLinearInj : Function.Injective a.linear := a.linear_injective_iff.mpr haInj
  have haLinearSurj : Function.Surjective a.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp haLinearInj
  have haBij : Function.Bijective a := a.linear_bijective_iff.mp
    ⟨haLinearInj, haLinearSurj⟩
  let e : Plane ≃ᵃ[ℝ] Plane := AffineEquiv.ofBijective haBij
  refine ⟨e.symm.toAffineMap, fun y hy => ?_⟩
  obtain ⟨x, hxt, rfl⟩ := hsTarget hy
  have hxA : x ∈ A := by
    rw [← F.support_eq]
    exact F.complex.cellCarrier_subset_support ht hxt
  change F.inverseOn (f x) = e.symm (f x)
  rw [F.inverseOn_apply hxA, hfa hxt]
  exact (e.symm_apply_apply x).symm

/-- A common target refinement together with all data needed to pull it back through a finite
PL homeomorphism.  This is the relative-subdivision package used when a prescribed target mesh
introduces new vertices on the boundary of a polygonal face. -/
structure PullbackSubdivision (F : FinitePLHomeomorphBetween f A B)
    (R : PlaneComplex) where
  /-- The `target` declaration. -/
  target : PlaneComplex
  target_support : target.support = B
  target_pure : target.IsPure2
  target_subdivides_certificate : target.Subdivides F.targetComplex
  target_subdivides_given : target.Subdivides R
  target_vertex_mem_support : ∀ v : target.Vertex,
    target.position v ∈ target.support
  inverseAffine : ∀ s ∈ target.simplexes,
    IsAffineOn F.inverseOn (target.cellCarrier s)

/-- Pull a prescribed pure finite target mesh back through a certified finite PL
homeomorphism.  A common refinement is taken first, so no compatibility between the supplied
mesh and the certificate's original target complex is required. -/
noncomputable def pullbackSubdivision
    (F : FinitePLHomeomorphBetween f A B) (R : PlaneComplex)
    (hRpure : R.IsPure2) (hRsupport : R.support = B) :
    PullbackSubdivision F R := by
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure hRpure
    (F.targetComplex_support.trans hRsupport.symm)
  let T₀ : PlaneComplex := common.choose.toPlaneComplex
  let T : PlaneComplex := PlaneComplex.active T₀
  have hTcert : T.Subdivides F.targetComplex :=
    PlaneComplex.active_subdivides_left common.choose_spec.1
  have hTgiven : T.Subdivides R :=
    PlaneComplex.active_subdivides_left common.choose_spec.2
  have hTpure : T.IsPure2 :=
    PlaneComplex.IsPure2.active T₀ common.choose.toPlaneComplex_isPure2
  have hTsupport : T.support = B := hTcert.1.trans F.targetComplex_support
  have hTvertex : ∀ v : T.Vertex, T.position v ∈ T.support := by
    intro v
    change T₀.position v.1 ∈ T.support
    rw [T₀.active_support]
    exact v.2
  exact
    { target := T
      target_support := hTsupport
      target_pure := hTpure
      target_subdivides_certificate := hTcert
      target_subdivides_given := hTgiven
      target_vertex_mem_support := hTvertex
      inverseAffine := F.inverseOn_affineOn_of_subdivides_targetComplex hTcert }

namespace PullbackSubdivision

variable {f : Plane → Plane} {A B : Set Plane}
  {F : FinitePLHomeomorphBetween f A B} {R : PlaneComplex}
  (P : PullbackSubdivision F R)

theorem inverseOn_injOn_target : Set.InjOn F.inverseOn P.target.support := by
  rw [P.target_support]
  exact F.inverseOn_injOn

/-- The actual source complex obtained by mapping the common target refinement through the
certified inverse.  It has the same vertex and simplex labels as the target refinement. -/
noncomputable def source : PlaneComplex :=
  P.target.mapComplexOn F.inverseOn P.target_vertex_mem_support
    P.inverseOn_injOn_target P.inverseAffine

@[simp] theorem source_simplexes : P.source.simplexes = P.target.simplexes := rfl

theorem inverseOn_image_target : F.inverseOn '' B = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact F.inverseOn_mem hy
  · intro x hx
    refine ⟨f x, ?_, F.inverseOn_apply hx⟩
    rw [← F.image_eq]
    exact ⟨x, hx, rfl⟩

theorem source_support : P.source.support = A := by
  rw [source, P.target.mapComplexOn_support F.inverseOn
    P.target_vertex_mem_support P.inverseOn_injOn_target P.inverseAffine,
    P.target_support, inverseOn_image_target (F := F)]

theorem source_pure : P.source.IsPure2 :=
  PlaneComplex.IsPure2.mapComplexOn P.target P.target_pure F.inverseOn
    P.target_vertex_mem_support P.inverseOn_injOn_target P.inverseAffine

theorem source_cellCarrier (s : Finset P.target.Vertex)
    (hs : s ∈ P.target.simplexes) :
    P.source.cellCarrier s = F.inverseOn '' P.target.cellCarrier s := by
  exact P.target.mapComplexOn_cellCarrier F.inverseOn P.target_vertex_mem_support
    P.inverseOn_injOn_target P.inverseAffine hs

/-- Corresponding source and target faces are carried exactly onto one another by the
original map. -/
theorem image_source_cellCarrier (s : Finset P.target.Vertex)
    (hs : s ∈ P.target.simplexes) :
    f '' P.source.cellCarrier s = P.target.cellCarrier s := by
  rw [P.source_cellCarrier s hs]
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    have hzB : z ∈ B := by
      rw [← P.target_support]
      exact P.target.cellCarrier_subset_support hs hz
    simpa only [F.apply_inverseOn hzB] using hz
  · intro y hy
    have hyB : y ∈ B := by
      rw [← P.target_support]
      exact P.target.cellCarrier_subset_support hs hy
    exact ⟨F.inverseOn y, ⟨y, hy, rfl⟩, F.apply_inverseOn hyB⟩

end PullbackSubdivision

/-- Postcomposition by an ambient finite PL homeomorphism preserves finite PL cell
homeomorphisms.  A common target subdivision is pulled back through the first map. -/
noncomputable def transAmbient (F : FinitePLHomeomorphBetween f A B)
    {h : Plane ≃ₜ Plane} (G : FinitePLHomeomorphOn h B) :
    FinitePLHomeomorphBetween (h ∘ f) A (h '' B) := by
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure G.pure
    (F.targetComplex_support.trans G.support_eq.symm)
  let R₀ : PlaneComplex := common.choose.toPlaneComplex
  let R : PlaneComplex := PlaneComplex.active R₀
  have hRtarget : R.Subdivides F.targetComplex :=
    PlaneComplex.active_subdivides_left common.choose_spec.1
  have hRG : R.Subdivides G.complex :=
    PlaneComplex.active_subdivides_left common.choose_spec.2
  have hRpure : R.IsPure2 :=
    PlaneComplex.IsPure2.active R₀ common.choose.toPlaneComplex_isPure2
  have hRsupport : R.support = B :=
    hRtarget.1.trans F.targetComplex_support
  have hRvertex : ∀ v : R.Vertex, R.position v ∈ R.support := by
    intro v
    change R₀.position v.1 ∈ R.support
    rw [R₀.active_support]
    exact v.2
  have hinverseAffine : ∀ s ∈ R.simplexes,
      IsAffineOn F.inverseOn (R.cellCarrier s) :=
    F.inverseOn_affineOn_of_subdivides_targetComplex hRtarget
  have hinverseInj : Set.InjOn F.inverseOn R.support := by
    rw [hRsupport]
    exact F.inverseOn_injOn
  have hinverseImage : F.inverseOn '' B = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact F.inverseOn_mem hy
    · intro x hx
      refine ⟨f x, ?_, F.inverseOn_apply hx⟩
      rw [← F.image_eq]
      exact ⟨x, hx, rfl⟩
  let Finv : FinitePLHomeomorphBetween F.inverseOn B A :=
    { complex := R
      support_eq := hRsupport
      pure := hRpure
      vertex_mem_support := hRvertex
      affineOn := hinverseAffine
      injOn := F.inverseOn_injOn
      image_eq := hinverseImage }
  let S : PlaneComplex := Finv.targetComplex
  have hSsupport : S.support = A := Finv.targetComplex_support
  have hSpure : S.IsPure2 := Finv.targetComplex_pure
  have hfLikeAffine : ∀ s ∈ S.simplexes,
      IsAffineOn Finv.inverseOn (S.cellCarrier s) :=
    Finv.inverseOn_affineOn_of_subdivides_targetComplex
      (PlaneComplex.Subdivides.refl S)
  have hfLike_eq : Set.EqOn Finv.inverseOn f A := by
    intro x hx
    have hfxB : f x ∈ B := by
      rw [← F.image_eq]
      exact ⟨x, hx, rfl⟩
    have hfinvB : Finv.inverseOn x ∈ B := Finv.inverseOn_mem hx
    apply F.inverseOn_injOn hfinvB hfxB
    rw [Finv.apply_inverseOn hx, F.inverseOn_apply hx]
  have hfAffine : ∀ s ∈ S.simplexes, IsAffineOn f (S.cellCarrier s) := by
    intro s hs
    obtain ⟨a, ha⟩ := hfLikeAffine s hs
    refine ⟨a, fun x hx => ?_⟩
    rw [← hfLike_eq (hSsupport ▸ S.cellCarrier_subset_support hs hx)]
    exact ha hx
  have hgAffine : ∀ s ∈ R.simplexes, IsAffineOn h (R.cellCarrier s) := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := hRG.2 s hs
    exact (G.affineOn u hu).mono hsu
  have hmaps : ∀ s ∈ S.simplexes,
      Set.MapsTo f (S.cellCarrier s) (R.cellCarrier s) := by
    intro s hs x hx
    have hsR : s ∈ R.simplexes := hs
    have hcell : S.cellCarrier s = F.inverseOn '' R.cellCarrier s := by
      exact R.mapComplexOn_cellCarrier F.inverseOn hRvertex hinverseInj
        hinverseAffine hsR
    rw [hcell] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyB : y ∈ B := by
      rw [← hRsupport]
      exact R.cellCarrier_subset_support hsR hy
    rw [F.apply_inverseOn hyB]
    exact hy
  refine {
    complex := S
    support_eq := hSsupport
    pure := hSpure
    vertex_mem_support := ?_
    affineOn := ?_
    injOn := fun x hx y hy hxy => F.injOn hx hy (h.injective hxy)
    image_eq := ?_ }
  · intro v
    exact Finv.targetComplex_vertex_mem_support v
  · intro s hs
    exact (hgAffine s hs).comp (hfAffine s hs) (hmaps s hs)
  · rw [Set.image_comp, F.image_eq]

end FinitePLHomeomorphBetween

namespace FinitePLHomeomorphOn

variable {h g : Plane ≃ₜ Plane} {A : Set Plane}

/-- Reindex a finite PL witness along an equality of its underlying polyhedron. -/
def congrSet (F : FinitePLHomeomorphOn h A) {B : Set Plane} (hAB : A = B) :
    FinitePLHomeomorphOn h B where
  complex := F.complex
  support_eq := F.support_eq.trans hAB
  pure := F.pure
  affineOn := F.affineOn

/-- Reindex a certificate along equality of ambient homeomorphisms. -/
def congrHomeomorph (F : FinitePLHomeomorphOn h A) {g : Plane ≃ₜ Plane} (hg : h = g) :
    FinitePLHomeomorphOn g A := hg ▸ F

/-- Forget the explicit pure witness and retain the ordinary finite PL-on-set predicate. -/
theorem isPLOnSet (F : FinitePLHomeomorphOn h A) : IsPLOnSet A h := by
  exact ⟨F.complex, F.support_eq, F.complex, PlaneComplex.Subdivides.refl F.complex,
    F.affineOn⟩

/-- The geometric target complex obtained by mapping source vertices and faces. -/
noncomputable def targetComplex (F : FinitePLHomeomorphOn h A) : PlaneComplex :=
  F.complex.mapComplex h h.injective F.affineOn

theorem targetComplex_support (F : FinitePLHomeomorphOn h A) :
    F.targetComplex.support = h '' A := by
  rw [targetComplex, F.complex.mapComplex_support h h.injective F.affineOn, F.support_eq]

theorem targetComplex_pure (F : FinitePLHomeomorphOn h A) :
    F.targetComplex.IsPure2 :=
  PlaneComplex.IsPure2.mapComplex F.complex F.pure h h.injective F.affineOn

/-- The inverse homeomorphism is PL on the exact image polyhedron. -/
noncomputable def symm (F : FinitePLHomeomorphOn h A) :
    FinitePLHomeomorphOn h.symm (h '' A) where
  complex := F.targetComplex
  support_eq := F.targetComplex_support
  pure := F.targetComplex_pure
  affineOn := F.complex.inverse_affineOn_of_subdivides_mapComplex F.pure h F.affineOn
    (PlaneComplex.Subdivides.refl F.targetComplex)

/-- Identity is affine on every face of an explicit pure complex. -/
def refl (K : PlaneComplex) (hpure : K.IsPure2) :
    FinitePLHomeomorphOn (Homeomorph.refl Plane) K.support where
  complex := K
  support_eq := rfl
  pure := hpure
  affineOn := by
    intro s hs
    exact ⟨AffineMap.id ℝ Plane, fun _ _ => rfl⟩

/-- Finite PL witnesses compose.  The proof takes a common target subdivision, pulls it back
through the first homeomorphism, and composes the two affine witnesses face by face. -/
noncomputable def trans (F : FinitePLHomeomorphOn h A)
    (G : FinitePLHomeomorphOn g (h '' A)) :
    FinitePLHomeomorphOn (h.trans g) A := by
  let P := F.targetComplex
  have hPG : P.support = G.complex.support :=
    F.targetComplex_support.trans G.support_eq.symm
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure G.pure hPG
  let Rmesh := common.choose
  have hRP := common.choose_spec.1
  have hRG := common.choose_spec.2
  let R := Rmesh.toPlaneComplex
  have hRpure : R.IsPure2 := Rmesh.toPlaneComplex_isPure2
  have hinvAffine : ∀ s ∈ R.simplexes, IsAffineOn h.symm (R.cellCarrier s) :=
    F.complex.inverse_affineOn_of_subdivides_mapComplex F.pure h F.affineOn hRP
  let Q : PlaneComplex := R.mapComplex h.symm h.symm.injective hinvAffine
  have hQsupport : Q.support = A := by
    change (R.mapComplex h.symm h.symm.injective hinvAffine).support = A
    rw [R.mapComplex_support h.symm h.symm.injective hinvAffine,
      hRP.1, F.targetComplex_support]
    ext x
    simp
  have hQpure : Q.IsPure2 :=
    PlaneComplex.IsPure2.mapComplex R hRpure h.symm h.symm.injective hinvAffine
  have hhAffine : ∀ s ∈ Q.simplexes, IsAffineOn h (Q.cellCarrier s) := by
    exact R.inverse_affineOn_of_subdivides_mapComplex hRpure h.symm hinvAffine
      (PlaneComplex.Subdivides.refl Q)
  refine {
    complex := Q
    support_eq := hQsupport
    pure := hQpure
    affineOn := ?_ }
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hRG.2 s hs
  have hgAffine : IsAffineOn g (R.cellCarrier s) := (G.affineOn u hu).mono hsu
  have hmaps : Set.MapsTo h (Q.cellCarrier s) (R.cellCarrier s) := by
    intro x hx
    change x ∈ (R.mapComplex h.symm h.symm.injective hinvAffine).cellCarrier s at hx
    rw [R.mapComplex_cellCarrier h.symm h.symm.injective hinvAffine hs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  exact hgAffine.comp (hhAffine s hs) hmaps

/-- A finite PL homeomorphism supported on a compact patch is finite PL on every finite plane
polyhedron.  The source is cut by all barycentric lines of the patch.  A resulting triangle
which meets the patch interior lies in one patch triangle; on every other triangle continuity
extends the identity from its interior to its closure. -/
noncomputable def extendByIdentity (F : FinitePLHomeomorphOn h A)
    (hfix : Set.EqOn h id Aᶜ) (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn h K.support := by
  let source := K.toTriangleMesh
  let target := F.complex.toTriangleMesh
  let R := source.refineTo target
  have htargetSupport : target.toPlaneComplex.support = A := by
    exact (F.complex.toTriangleMesh_support F.pure).trans F.support_eq
  refine {
    complex := R.toPlaneComplex
    support_eq := (source.refineTo_support target).trans (K.toTriangleMesh_support hKpure)
    pure := R.toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := R.mem_faces_iff.mp hs
  let T : R.Triangle := ⟨t, ht⟩
  by_cases hhit : (interior (R.triangleCarrier T.1) ∩
      target.toPlaneComplex.support).Nonempty
  · obtain ⟨U, hTU⟩ :=
      source.exists_target_triangle_of_refineTo_of_interior_inter_support target T hhit
    have hUcell : U.1 ∈ F.complex.cells := U.2
    have hUsimplex : U.1 ∈ F.complex.simplexes :=
      F.complex.mem_simplexes_of_mem_cells hUcell
    apply (F.affineOn U.1 hUsimplex).mono
    exact (convexHull_mono (Set.image_mono hst)).trans hTU
  · have heqInterior : Set.EqOn h id (interior (R.triangleCarrier T.1)) := by
      intro x hx
      apply hfix
      rw [Set.mem_compl_iff]
      intro hxA
      apply hhit
      exact ⟨x, hx, htargetSupport.symm ▸ hxA⟩
    have heqTriangle : Set.EqOn h id (R.triangleCarrier T.1) := by
      rw [← R.closure_interior_triangleCarrier T]
      exact heqInterior.closure h.continuous continuous_id
    exact ⟨AffineMap.id ℝ Plane,
      heqTriangle.mono (convexHull_mono (Set.image_mono hst))⟩

end FinitePLHomeomorphOn

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
