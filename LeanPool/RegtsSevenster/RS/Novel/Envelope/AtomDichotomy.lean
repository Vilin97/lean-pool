/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiSemisimple
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.AtomicIdempotents

/-!
# The Hom-dichotomy between atoms

An *atom* of the Karoubi envelope is an object whose endomorphisms
are the scalar line of a nonzero identity.  Between atoms, the
mixed-trace nondegeneracy forces the dichotomy: every nonzero
morphism composes with a partner to a nonzero scalar, hence is an
isomorphism.  This is the engine turning the atomic idempotent
decomposition into a semisimple-category structure.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-- An atom: the endomorphisms are scalars, and the identity is
nonzero. -/
structure IsAtom (S : Karoubi (SkeinObj f)) : Prop where
  scalar : ∀ x : End S, ∃ c : ℂ, x = c • 𝟙 S
  id_ne_zero : 𝟙 S ≠ 0

/-- Scalars act faithfully on a nonzero identity. -/
private theorem smul_id_injective {S : Karoubi (SkeinObj f)}
    (hS : 𝟙 S ≠ 0) {c d : ℂ}
    (h : c • 𝟙 S = d • 𝟙 S) : c = d := by
  by_contra hcd
  have hsub : (c - d) • 𝟙 S = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with hc | hid
  · exact hcd (sub_eq_zero.mp hc)
  · exact hS hid

/-- **The dichotomy**: a nonzero morphism between atoms is an
isomorphism. -/
theorem atom_iso_of_ne_zero {S T : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) (hT : IsAtom f T)
    {φ : S ⟶ T} (hφ : φ ≠ 0) :
    ∃ ψ : T ⟶ S, φ ≫ ψ = 𝟙 S ∧ ψ ≫ φ = 𝟙 T := by
  -- Nondegeneracy: some partner has nonvanishing closure trace.
  have hpartner : ∃ b : T ⟶ S,
      HomSpace.traceMap f.val S.X.arity (φ.f ≫ b.f) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hφ (karoubiHom_eq_zero_of_traces_vanish f φ
      (fun b => hall b))
  obtain ⟨b, hb⟩ := hpartner
  -- The composite is a nonzero scalar on the source atom.
  obtain ⟨c, hc⟩ := hS.scalar (φ ≫ b)
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    have : (φ ≫ b).f = 0 := by rw [hc]; rfl
    rw [show (φ ≫ b).f = φ.f ≫ b.f from rfl] at this
    rw [this, map_zero] at hb
    exact hb rfl
  -- Normalize to a one-sided inverse.
  refine ⟨c⁻¹ • b, ?_, ?_⟩
  · rw [CategoryTheory.Linear.comp_smul, hc, smul_smul,
      inv_mul_cancel₀ hcne, one_smul]
  · -- The reverse composite is an idempotent scalar on the
    -- target atom; it cannot be zero, hence is the identity.
    obtain ⟨d, hd⟩ := hT.scalar ((c⁻¹ • b) ≫ φ)
    have hidem : ((c⁻¹ • b) ≫ φ) ≫ ((c⁻¹ • b) ≫ φ) =
        (c⁻¹ • b) ≫ φ := by
      rw [show ((c⁻¹ • b) ≫ φ) ≫ ((c⁻¹ • b) ≫ φ) =
        (c⁻¹ • b) ≫ (φ ≫ (c⁻¹ • b)) ≫ φ from by
          simp only [Category.assoc]]
      rw [CategoryTheory.Linear.comp_smul, hc, smul_smul,
        inv_mul_cancel₀ hcne, one_smul, Category.id_comp]
    rw [hd] at hidem ⊢
    rw [show (d • 𝟙 T) ≫ (d • 𝟙 T) = (d * d) • 𝟙 T from by
      rw [CategoryTheory.Linear.smul_comp,
        CategoryTheory.Linear.comp_smul, Category.id_comp,
        smul_smul]] at hidem
    have hdd := smul_id_injective f hT.id_ne_zero hidem
    have hcases : d = 0 ∨ d = 1 := by
      have h0 : d * (d - 1) = 0 := by
        rw [mul_sub, mul_one, hdd, sub_self]
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases hcases with hd0 | hd1
    · -- d = 0 would kill φ
      exfalso
      rw [hd0, zero_smul] at hd
      have hφ0 : φ = 0 := by
        have h1 : φ ≫ ((c⁻¹ • b) ≫ φ) = φ ≫ 0 := by
          rw [hd]
        rw [show φ ≫ ((c⁻¹ • b) ≫ φ) =
          (φ ≫ (c⁻¹ • b)) ≫ φ from by
            simp only [Category.assoc]] at h1
        rw [CategoryTheory.Linear.comp_smul, hc, smul_smul,
          inv_mul_cancel₀ hcne, one_smul,
          Category.id_comp] at h1
        rw [h1, Limits.comp_zero]
      exact hφ hφ0
    · rw [hd1, one_smul]

/-! ### Atoms from atomic idempotents -/

/-- The Karoubi object cut out of `X` by an idempotent of its
endomorphism algebra. -/
@[reducible] noncomputable def cutBy (X : Karoubi (SkeinObj f))
    {eK : End X} (he : IsIdempotentElem eK) :
    Karoubi (SkeinObj f) where
  X := X.X
  p := eK.f
  idem := by
    have := congrArg Karoubi.Hom.f (he : eK * eK = eK)
    exact this

/-- The object cut out by an atomic idempotent is an atom. -/
theorem isAtom_cutBy (X : Karoubi (SkeinObj f))
    {eK : End X} (he : IsAtomicIdempotent eK) :
    IsAtom f (cutBy f X he.idem) := by
  constructor
  · intro x
    -- Lift to the ambient endomorphism algebra and use the
    -- corner-scalar property.
    have habs₁ : eK.f ≫ x.f = x.f := Karoubi.p_comp x
    have habs₂ : x.f ≫ eK.f = x.f := Karoubi.comp_p x
    have hyc : X.p ≫ x.f ≫ X.p = x.f := by
      rw [show X.p ≫ x.f ≫ X.p =
        X.p ≫ (eK.f ≫ x.f ≫ eK.f) ≫ X.p from by
          rw [show eK.f ≫ x.f ≫ eK.f = x.f from by
            rw [habs₂, habs₁]]]
      rw [show X.p ≫ (eK.f ≫ x.f ≫ eK.f) ≫ X.p =
        (X.p ≫ eK.f) ≫ x.f ≫ (eK.f ≫ X.p) from by
          simp only [Category.assoc]]
      rw [Karoubi.p_comp, Karoubi.comp_p, habs₂, habs₁]
    obtain ⟨c, hc⟩ := he.corner_scalar ⟨x.f, hyc⟩
    refine ⟨c, ?_⟩
    apply Karoubi.hom_ext
    have hcf := congrArg Karoubi.Hom.f hc
    rw [show (eK * ⟨x.f, hyc⟩ * eK).f =
      eK.f ≫ x.f ≫ eK.f from by
        show ((eK * ⟨x.f, hyc⟩) * eK).f = _
        rw [show ((eK * ⟨x.f, hyc⟩) * eK).f =
          eK.f ≫ (eK * ⟨x.f, hyc⟩).f from rfl]
        rw [show (eK * ⟨x.f, hyc⟩).f = x.f ≫ eK.f from rfl]] at hcf
    rw [habs₂, habs₁] at hcf
    rw [hcf]
    rfl
  · intro h
    apply he.ne_zero
    apply Karoubi.hom_ext
    have := congrArg Karoubi.Hom.f h
    rw [show Karoubi.Hom.f (𝟙 (cutBy f X he.idem)) = eK.f
      from rfl] at this
    rw [this]
    rfl

end RS
