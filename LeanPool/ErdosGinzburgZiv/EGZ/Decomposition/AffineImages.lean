/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation

/-!
# Rational affine images and their faces

Integral affine maps preserve rational points, hence map rational polytopes
to rational polytopes. An injective affine map gives an order isomorphism
between the source and image face lattices, with explicit carrier formulas.
These constructions place a lineage's varying coordinate spaces inside its
initial coordinate space for the common-measure face-counting argument.
-/

open scoped BigOperators

namespace EGZ

namespace IntegralAffineMap

theorem real_isRational {m n : ℕ} (A : IntegralAffineMap m n)
    {q : RealCoord m} (hq : IsRational q) : IsRational (A.real q) := by
  classical
  choose a ha using hq
  intro i
  refine ⟨scalarExtension ℚ A.toIntAffineMap a i, ?_⟩
  have hreal : scalarExtension ℝ A.toIntAffineMap = A.real :=
    congrArg IntegralAffineMap.real (ofIntAffineMap_toIntAffineMap A)
  rw [← hreal, scalarExtension_apply, scalarExtension_apply]
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, ha]

end IntegralAffineMap

namespace RationalPolytope

variable {l m n : ℕ}

/-- Image under an affine map which preserves rational coordinates. The
image carrier is definitionally the set-theoretic affine image. -/
noncomputable def affineImage (P : RationalPolytope m)
    (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) : RationalPolytope n := by
  classical
  have hcarrier : A '' P.carrier = convexHull ℝ (↑(P.generators.image A) : Set (RealCoord n)) := by
    rw [P.carrier_eq_convexHull, AffineMap.image_convexHull, Finset.coe_image]
  exact
    { carrier := A '' P.carrier
      generators := P.generators.image A
      generators_nonempty := P.generators_nonempty.image A
      generators_rational := by
        rintro q hq
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
        exact hAq z (P.generators_rational z hz)
      carrier_eq_convexHull := hcarrier
      finite_integral := by rw [hcarrier]; exact finite_integral_convexHull _ }

@[simp]
theorem affineImage_carrier (P : RationalPolytope m)
    (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) :
    (P.affineImage A hAq).carrier = A '' P.carrier := rfl

/-- Integral affine image of a rational polytope. Injectivity is not needed. -/
noncomputable abbrev image (P : RationalPolytope m) (A : IntegralAffineMap m n) :
    RationalPolytope n := P.affineImage A.real (fun _ ↦ A.real_isRational)

@[simp]
theorem image_carrier (P : RationalPolytope m) (A : IntegralAffineMap m n) :
    (P.image A).carrier = A.real '' P.carrier := rfl

/-- Commuting maps and source-polytope containment give nested image
polytopes even when the two source coordinate dimensions differ. -/
theorem affineImage_subset (P : RationalPolytope l) (Q : RationalPolytope m)
    (A : RealCoord l →ᵃ[ℝ] RealCoord n) (B : RealCoord m →ᵃ[ℝ] RealCoord n)
    (T : RealCoord l →ᵃ[ℝ] RealCoord m)
    (hAq : ∀ q, IsRational q → IsRational (A q))
    (hBq : ∀ q, IsRational q → IsRational (B q))
    (hT : Set.MapsTo T P.carrier Q.carrier)
    (hcomm : ∀ q ∈ P.carrier, A q = B (T q)) :
    (P.affineImage A hAq).carrier ⊆ (Q.affineImage B hBq).carrier := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨T q, hT hq, (hcomm q hq).symm⟩

namespace Face

variable {P : RationalPolytope m}

/-- An injective affine map carries every exposed face to an exposed face
of the image, using an affine left inverse to transport its functional. -/
noncomputable def affineImage (Γ : P.Face) (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A) :
    (P.affineImage A hAq).Face where
  carrier := A '' Γ.carrier
  is_exposed := by
    obtain ⟨functional, level, hle, hcarrier⟩ := Γ.is_exposed
    refine ⟨functional.comp (affineLeftInverse A), level, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      simpa only [AffineMap.comp_apply, affineLeftInverse_apply A hA] using hle q hq
    · ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        rw [hcarrier] at hq
        exact ⟨⟨q, hq.1, rfl⟩, by
          simpa only [AffineMap.comp_apply, affineLeftInverse_apply A hA] using hq.2⟩
      · rintro ⟨⟨q, hq, rfl⟩, heq⟩
        refine ⟨q, ?_, rfl⟩
        rw [hcarrier]
        exact ⟨hq, by
          simpa only [AffineMap.comp_apply, affineLeftInverse_apply A hA] using heq⟩
  nonempty := Γ.nonempty.image A

@[simp]
theorem affineImage_carrier (Γ : P.Face) (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A) :
    (Γ.affineImage A hAq hA).carrier = A '' Γ.carrier := rfl

/-- Image of a face under an injective integral affine map. -/
noncomputable abbrev image (Γ : P.Face) (A : IntegralAffineMap m n)
    (hA : Function.Injective A.real) : (P.image A).Face :=
  Γ.affineImage A.real (fun _ ↦ A.real_isRational) hA

@[simp]
theorem image_carrier (Γ : P.Face) (A : IntegralAffineMap m n)
    (hA : Function.Injective A.real) : (Γ.image A hA).carrier = A.real '' Γ.carrier := rfl

/-- Pull back any face of an image polytope. The image description supplies
the required nonemptiness automatically. -/
noncomputable def affineImagePullback (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q))
    (Δ : (P.affineImage A hAq).Face) : P.Face :=
  Δ.preimage A (fun q hq ↦ ⟨q, hq, rfl⟩) (by
    obtain ⟨z, hz⟩ := Δ.nonempty
    obtain ⟨q, hq, rfl⟩ := Δ.subset_polytope hz
    exact ⟨q, hq, hz⟩)

@[simp]
theorem affineImagePullback_carrier (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q))
    (Δ : (P.affineImage A hAq).Face) :
    (Δ.affineImagePullback A hAq).carrier = P.carrier ∩ A ⁻¹' Δ.carrier := rfl

@[simp]
theorem affineImagePullback_affineImage (Γ : P.Face) (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A) :
    (Γ.affineImage A hAq hA).affineImagePullback A hAq = Γ := by
  apply Face.ext
  rw [affineImagePullback_carrier, affineImage_carrier, Set.preimage_image_eq _ hA]
  exact Set.inter_eq_right.mpr Γ.subset_polytope

@[simp]
theorem affineImage_affineImagePullback (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A)
    (Δ : (P.affineImage A hAq).Face) :
    (Δ.affineImagePullback A hAq).affineImage A hAq hA = Δ := by
  apply Face.ext
  rw [affineImage_carrier, affineImagePullback_carrier, Set.image_inter_preimage]
  exact Set.inter_eq_right.mpr Δ.subset_polytope

theorem affineImage_ssubset_iff (Γ Δ : P.Face) (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A) :
    (Γ.affineImage A hAq hA).carrier ⊂ (Δ.affineImage A hAq hA).carrier ↔
      Γ.carrier ⊂ Δ.carrier := by
  simp only [affineImage_carrier, Set.ssubset_def, Set.image_subset_image_iff hA]

/-- Image coordinates preserve the no-repeated-restricted-face condition
when all polytopes are already expressed in one source coordinate space. -/
theorem image_inter_carrier_eq_iff {Q : RationalPolytope m} (Γ : P.Face) (Δ : Q.Face)
    (A : IntegralAffineMap m n) (hA : Function.Injective A.real) :
    (Γ.image A hA).carrier ∩ (Q.image A).carrier = (Δ.image A hA).carrier ↔
      Γ.carrier ∩ Q.carrier = Δ.carrier := by
  rw [image_carrier, RationalPolytope.image_carrier, image_carrier, ← Set.image_inter hA]
  exact hA.image_injective.eq_iff

end Face

/-- The full face lattice is unchanged by injective affine coordinates. -/
noncomputable def faceAffineImageEquiv (P : RationalPolytope m)
    (A : RealCoord m →ᵃ[ℝ] RealCoord n)
    (hAq : ∀ q, IsRational q → IsRational (A q)) (hA : Function.Injective A) :
    P.Face ≃o (P.affineImage A hAq).Face where
  toFun Γ := Γ.affineImage A hAq hA
  invFun Δ := Δ.affineImagePullback A hAq
  left_inv Γ := Γ.affineImagePullback_affineImage A hAq hA
  right_inv Δ := Δ.affineImage_affineImagePullback A hAq hA
  map_rel_iff' := Set.image_subset_image_iff hA

/-- Order isomorphism between faces of a polytope and its injective affine image. -/
noncomputable abbrev faceImageEquiv (P : RationalPolytope m) (A : IntegralAffineMap m n)
    (hA : Function.Injective A.real) : P.Face ≃o (P.image A).Face :=
  P.faceAffineImageEquiv A.real (fun _ ↦ A.real_isRational) hA

end RationalPolytope

/-- For two injective coordinate maps, equality of a later image face with
the restricted old image face is exactly equality with the pulled-back face.
This formula allows the two source coordinate dimensions to differ. -/
theorem affineImage_inter_comp_eq_iff {l m n : ℕ}
    (A : RealCoord m →ᵃ[ℝ] RealCoord n) (T : RealCoord l →ᵃ[ℝ] RealCoord m)
    (hA : Function.Injective A) (hT : Function.Injective T)
    (S : Set (RealCoord m)) (P Γ : Set (RealCoord l)) :
    A '' S ∩ (A.comp T) '' P = (A.comp T) '' Γ ↔ P ∩ T ⁻¹' S = Γ := by
  change A '' S ∩ (A ∘ T) '' P = (A ∘ T) '' Γ ↔ _
  rw [Set.image_comp, Set.image_comp, ← Set.image_inter hA, hA.image_injective.eq_iff]
  rw [Set.inter_comm, ← Set.image_inter_preimage, hT.image_injective.eq_iff]

end EGZ
