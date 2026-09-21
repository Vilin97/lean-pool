/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvDeligne

/-!
# Semisimplicity of the envelope

The Deligne semisimplicity hypothesis for the envelope: every
object is a finite biproduct of simple objects.  The endomorphism
algebra is finite-dimensional and semisimple by the factorial trace
obstruction, so the identity splits into a complete orthogonal
family of atomic idempotents; each cuts out a corner object with
scalar endomorphisms, which is simple because monomorphisms split
in the envelope, and the object is the biproduct of its corners.
-/

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.Limits

universe v u

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Corner cuts of Karoubi objects (general) -/

section GenericCut

variable {D : Type u}

/-- The corner object cut out of a Karoubi object by an
idempotent endomorphism. -/
noncomputable def karoubiCorner
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    Karoubi D :=
  ⟨X.X, e.f, congrArg Karoubi.Hom.f he⟩

/-- The corner inclusion. -/
noncomputable def cornerIncl
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    karoubiCorner X he ⟶ X :=
  ⟨e.f, by
    show e.f ≫ e.f ≫ X.p = e.f
    rw [Karoubi.comp_p]
    exact congrArg Karoubi.Hom.f he⟩

/-- The corner projection. -/
noncomputable def cornerProj
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    X ⟶ karoubiCorner X he :=
  ⟨e.f, by
    show X.p ≫ e.f ≫ e.f = e.f
    rw [show (e.f ≫ e.f : X.X ⟶ X.X) = e.f from
      congrArg Karoubi.Hom.f he, Karoubi.p_comp]⟩

/-- The corner is a retract: including then projecting is the
identity on it. -/
theorem cornerIncl_proj
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    cornerIncl X he ≫ cornerProj X he = 𝟙 (karoubiCorner X he) := by
  apply Karoubi.hom_ext
  show e.f ≫ e.f = e.f
  exact congrArg Karoubi.Hom.f he

/-- Projecting then including is the idempotent. -/
theorem cornerProj_incl
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    cornerProj X he ≫ cornerIncl X he = e := by
  apply Karoubi.hom_ext
  exact congrArg Karoubi.Hom.f he

/-- The inclusion is absorbed by the idempotent. -/
theorem cornerIncl_absorb
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    cornerIncl X he ≫ e = cornerIncl X he := by
  apply Karoubi.hom_ext
  show e.f ≫ e.f = e.f
  exact congrArg Karoubi.Hom.f he

/-- And so is the projection. -/
theorem cornerProj_absorb
    [Category.{v} D] (X : Karoubi D) {e : End X} (he : IsIdempotentElem e) :
    e ≫ cornerProj X he = cornerProj X he := by
  apply Karoubi.hom_ext
  show e.f ≫ e.f = e.f
  exact congrArg Karoubi.Hom.f he

/-- Cross-composites of distinct orthogonal corners vanish. -/
theorem cornerIncl_proj_orthogonal
    [Category.{v} D] [Preadditive D] (X : Karoubi D) {e : End X}
    (he : IsIdempotentElem e)
    {e' : End X} (he' : IsIdempotentElem e')
    (horth : e' * e = 0) :
    cornerIncl X he ≫ cornerProj X he' = 0 := by
  apply Karoubi.hom_ext
  show e.f ≫ e'.f = (0 : X.X ⟶ X.X)
  exact congrArg Karoubi.Hom.f horth

end GenericCut

/-! ### Scalar corners are simple in the envelope -/

/-- An envelope object with scalar endomorphism algebra and
nonzero identity is simple: monomorphisms split, and a split
idempotent scalar is `0` or `1`. -/
theorem env_simple_of_scalar_end (E : Env f) (hne : 𝟙 E ≠ 0)
    (hsc : ∀ x : End E, ∃ c : ℂ, x = c • 𝟙 E) :
    Simple E := by
  constructor
  intro Y g hMono
  constructor
  · intro hIso hg
    obtain ⟨r, _, hr2⟩ := hIso.out
    rw [hg, comp_zero] at hr2
    exact hne hr2.symm
  · intro hg
    obtain ⟨r, hr⟩ := env_mono_split f g
    obtain ⟨c, hc⟩ := hsc (r ≫ g)
    have hidem : (r ≫ g) ≫ (r ≫ g) = r ≫ g := by
      rw [assoc, ← assoc g r g, hr, id_comp]
    rw [hc] at hidem
    have hcc : (c * c - c) • 𝟙 E = 0 := by
      rw [sub_smul, mul_smul]
      rw [show (c • c • 𝟙 E : End E) =
        (c • 𝟙 E) ≫ (c • 𝟙 E) from by
          rw [CategoryTheory.Linear.smul_comp,
            CategoryTheory.Linear.comp_smul, comp_id],
        hidem, sub_self]
    have hc2 : c * c = c := by
      rcases smul_eq_zero.mp hcc with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hne
    have h3 : c * (c - 1) = 0 := by
      rw [mul_sub, mul_one, hc2, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h1

    · exfalso
      rw [h0, zero_smul] at hc
      have : g = 0 := by
        rw [show g = (g ≫ r) ≫ g from by rw [hr, id_comp],
          assoc, hc, comp_zero]
      exact hg this
    · rw [sub_eq_zero.mp h1, one_smul] at hc
      exact ⟨⟨r, hr, hc⟩⟩

/-! ### The atomic corners of an envelope object -/

/-- The corner cut by an atomic idempotent has scalar
endomorphisms. -/
theorem env_corner_scalar (E : Env f) {e : End E}
    (he : IsAtomicIdempotent e)
    (x : End (karoubiCorner E he.idem)) :
    ∃ c : ℂ, x = c • 𝟙 (karoubiCorner E he.idem) := by
  set y : End E :=
    cornerProj E he.idem ≫ x ≫ cornerIncl E he.idem with hy
  obtain ⟨c, hc⟩ := he.corner_scalar y
  have habs : e ≫ y ≫ e = y := by
    rw [hy, ← assoc, ← assoc, cornerProj_absorb, assoc, assoc,
      cornerIncl_absorb]
  have hyc : y = c • e := by
    rw [← habs]
    calc e ≫ y ≫ e = e * y * e := rfl
      _ = c • e := hc
  refine ⟨c, ?_⟩
  have hx : x = cornerIncl E he.idem ≫ y ≫ cornerProj E he.idem := by
    rw [hy, ← assoc, ← assoc, cornerIncl_proj, id_comp, assoc,
      cornerIncl_proj, comp_id]
  rw [hx, hyc]
  have h1 : (c • e) ≫ cornerProj E he.idem =
      c • (e ≫ cornerProj E he.idem) :=
    CategoryTheory.Linear.smul_comp (R := ℂ) _ _ _ c e _
  have h2 : cornerIncl E he.idem ≫ (c • (e ≫ cornerProj E he.idem)) =
      c • (cornerIncl E he.idem ≫ e ≫ cornerProj E he.idem) :=
    CategoryTheory.Linear.comp_smul (R := ℂ) _ _ _ _ c _
  rw [h1, h2, cornerProj_absorb, cornerIncl_proj]

/-- The corner cut by an atomic idempotent has nonzero
identity. -/
theorem env_corner_id_ne_zero (E : Env f) {e : End E}
    (he : IsAtomicIdempotent e) :
    𝟙 (karoubiCorner E he.idem) ≠ 0 := by
  intro h
  apply he.ne_zero
  apply Karoubi.hom_ext
  have := congrArg Karoubi.Hom.f h
  exact this

/-! ### The biproduct decomposition -/

/-- **Semisimplicity of the envelope**: every object is a finite
biproduct of simple objects. -/
theorem env_deligneSemisimple :
    IsSemisimple (Env f) := by
  classical
  intro E
  haveI : FiniteDimensional ℂ (End E) := envHomFinite f E E
  haveI := envEnd_isSemisimpleRing f E
  obtain ⟨ι, hfin, e, hco, hatom⟩ :=
    exists_completeOrthogonal_atomic (A := End E)
  -- The corners, reindexed over `Fin n`.
  let q := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι,
    fun i => karoubiCorner E (hatom (q i)).idem, fun i => ?_, ⟨?_⟩⟩
  · exact env_simple_of_scalar_end f _
      (env_corner_id_ne_zero f E (hatom (q i)))
      (env_corner_scalar f E (hatom (q i)))
  -- The object is the biproduct of its corners over `ι`; then
  -- reindex along `q`.
  refine ?_ ≪≫ biproduct.whiskerEquiv (Fintype.equivFin ι)
    (fun j => eqToIso (by rw [Equiv.symm_apply_apply]))
  · exact
      { hom := biproduct.lift fun j => cornerProj E (hatom j).idem
        inv := biproduct.desc fun j => cornerIncl E (hatom j).idem
        hom_inv_id := by
          rw [biproduct.lift_desc]
          rw [show ∑ j, cornerProj E (hatom j).idem ≫
              cornerIncl E (hatom j).idem = ∑ j, e j from
            Finset.sum_congr rfl fun j _ => cornerProj_incl E _]
          exact hco.complete
        inv_hom_id := by
          apply biproduct.hom_ext
          intro j
          rw [assoc, biproduct.lift_π, id_comp]
          apply biproduct.hom_ext'
          intro i
          rw [biproduct.ι_desc_assoc, biproduct.ι_π]
          by_cases hij : i = j
          · subst hij
            rw [dif_pos rfl, eqToHom_refl, cornerIncl_proj]
          · rw [dif_neg hij]
            exact cornerIncl_proj_orthogonal E _ _
              (hco.ortho (Ne.symm hij)) }

end RS
