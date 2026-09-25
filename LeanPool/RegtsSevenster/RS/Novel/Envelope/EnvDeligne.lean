/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvInstances
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.LinearCategory
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SimpleUnit

/-!
# The Deligne hypotheses for the envelope

Two of the five hypothesis fields of the abstract Deligne input,
read off for the envelope: finite-dimensional Hom-spaces, by the
injection chain through the three layers, and scalar unit
endomorphisms, the arity-zero Hom space being the line of the
empty class, which the normalization `f ∅ = 1` keeps nonzero.

The other three are elsewhere: semisimplicity in
`EnvSemisimple.lean`, the tensor generator in `EnvGenerator.lean`,
and moderate growth in `EnvGrowth.lean`; `EnvDelignePackage.lean`
feeds all five to the cited statement.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
open MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Finite-dimensional Hom-spaces -/

/-- Envelope hom-spaces are finite-dimensional, by the injection
chain through the three layers. -/
noncomputable instance envHomFinite (P Q : Env f) :
    FiniteDimensional ℂ (P ⟶ Q) :=
  FiniteDimensional.of_injective
    (⟨⟨fun (x : P ⟶ Q) => x.f, fun _ _ => rfl⟩,
      fun _ _ => rfl⟩ :
      (P ⟶ Q) →ₗ[ℂ] (P.X ⟶ Q.X))
    (fun _ _ h => Karoubi.Hom.ext h)

/-- The envelope has finite-dimensional Hom-spaces. -/
theorem env_finDimHom : HasFinDimHom (Env f) :=
  fun P Q => envHomFinite f P Q

/-! ### Scalar unit endomorphisms -/

/-- The extraction of the arity-zero class from a unit
endomorphism. -/
noncomputable def unitExtract (x : End (𝟙_ (Env f))) :
    HomSpace f.val 0 :=
  ((x.f PUnit.unit PUnit.unit).f :
    SkeinObj.mk (f := f) 0 ⟶ SkeinObj.mk 0)

/-- The unit's endomorphisms inject into the arity-zero hom
space. -/
theorem unitExtract_injective :
    Function.Injective (unitExtract f) := by
  intro x y h
  apply Karoubi.hom_ext
  apply Mat_.hom_ext
  intro i j
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  exact Karoubi.hom_ext _ _ h

/-- It sends the identity to the empty class, which the
normalization keeps nonzero — so the unit endomorphisms are the
scalars. -/
theorem unitExtract_id :
    unitExtract f (𝟙 (𝟙_ (Env f))) =
      HomSpace.ofFragment f.val (strandBundle 0) := by
  change ((Karoubi.Hom.f (𝟙 (𝟙_ (Env f))) PUnit.unit
    PUnit.unit).f : SkeinObj.mk (f := f) 0 ⟶ SkeinObj.mk 0) =
    _
  rw [show Karoubi.Hom.f (𝟙 (𝟙_ (Env f))) =
    𝟙 ((𝟙_ (Env f)).X) from rfl]
  rw [Mat_.id_apply_self]
  rfl

/-- The identity of the unit is the empty class. -/
theorem unit_id_eq_emptyClass :
    HomSpace.ofFragment f.val (strandBundle 0) =
      emptyClass f.val :=
  HomSpace.ofFragment_congr f strandBundleZeroEmpty

/-- **Scalar unit endomorphisms.** -/
theorem env_endOne : HasScalarUnit (Env f) := by
  constructor
  · -- injective
    intro c d h
    have h2 : c • unitExtract f (𝟙 (𝟙_ (Env f))) =
        d • unitExtract f (𝟙 (𝟙_ (Env f))) := congrArg (unitExtract f) h
    rw [unitExtract_id, unit_id_eq_emptyClass] at h2
    by_contra hne
    have hsub : (c - d) • emptyClass f.val = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hz
    · exact hne (sub_eq_zero.mp hc)
    · exact emptyClass_ne_zero f hz
  · -- surjective
    intro x
    obtain ⟨c, hc⟩ := homSpace_zero_spanned f (unitExtract f x)
    refine ⟨c, ?_⟩
    apply unitExtract_injective f
    change c • unitExtract f (𝟙 (𝟙_ (Env f))) = unitExtract f x
    rw [unitExtract_id, unit_id_eq_emptyClass]
    exact hc.symm

end RS
