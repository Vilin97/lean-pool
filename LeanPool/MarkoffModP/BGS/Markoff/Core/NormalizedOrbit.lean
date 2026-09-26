/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Action
public import LeanPool.MarkoffModP.BGS.Markoff.Core.Normalization

/-!
# Markoff components in normalized coordinates

The Markoff group is defined on the original-coordinate surface.  This file transports its
permutations and component relation through `normalizationSurfaceEquiv`.  It also records the
specific group word for the fundamental rotation and proves that every iterate of the normalized
rotation stays in the same transported component.
-/

@[expose] public section

namespace BGS.Markoff

universe u

/-- The normalized Markoff surface as a subtype. -/
abbrev NormalizedMarkoffSurface (R : Type u) [CommRing R] :=
  {x : NormalizedPoint R // IsNormalizedMarkoff x}

/-- The fundamental rotation, restricted to the original-coordinate Markoff surface. -/
def rotate1Surface {R : Type u} [CommRing R] (x : MarkoffSurface R) :
    MarkoffSurface R :=
  ⟨rotate1 x.1, (isMarkoff_rotate1 x.1).2 x.property⟩

@[simp]
theorem coe_rotate1Surface {R : Type u} [CommRing R] (x : MarkoffSurface R) :
    ((rotate1Surface x : MarkoffSurface R) : Point R) = rotate1 x :=
  rfl

/-- The rotation fixing the first coordinate is `swap23` after the second Vieta involution. -/
theorem rotate1Surface_eq_swap23_after_vieta2 {R : Type u} [CommRing R]
    (x : MarkoffSurface R) :
    rotate1Surface x = swap23SurfacePerm R (vieta2SurfacePerm R x) := by
  apply Subtype.ext
  rfl

/-- The explicit element of `Gamma` realizing the fundamental rotation. -/
def gammaRotate1 (R : Type u) [CommRing R] : Gamma R :=
  gammaSwap23 R * gammaVieta2 R

@[simp]
theorem gammaRotate1_smul_surface {R : Type u} [CommRing R]
    (x : MarkoffSurface R) :
    gammaRotate1 R • x = rotate1Surface x := by
  rw [gammaRotate1, mul_smul, gammaVieta2_smul_surface, gammaSwap23_smul_surface]
  exact (rotate1Surface_eq_swap23_after_vieta2 x).symm

/-- A fundamental rotation is an honest move in the Markoff group. -/
theorem sameComponent_rotate1Surface {R : Type u} [CommRing R]
    (x : MarkoffSurface R) :
    SameComponent x (rotate1Surface x) := by
  rw [rotate1Surface_eq_swap23_after_vieta2]
  exact sameComponent_trans (sameComponent_vieta2 x)
    (sameComponent_swap23 (vieta2SurfacePerm R x))

/-- Conjugate an element of the original Markoff group to normalized coordinates. -/
def normalizedGammaPerm (R : Type u) [CommRing R] [Invertible (3 : R)]
    (g : Gamma R) : Equiv.Perm (NormalizedMarkoffSurface R) :=
  (normalizationSurfaceEquiv R).symm.trans
    ((g : Equiv.Perm (MarkoffSurface R)).trans (normalizationSurfaceEquiv R))

@[simp]
theorem normalizedGammaPerm_apply {R : Type u} [CommRing R] [Invertible (3 : R)]
    (g : Gamma R) (x : NormalizedMarkoffSurface R) :
    normalizedGammaPerm R g x =
      normalizationSurfaceEquiv R
        ((g : Equiv.Perm (MarkoffSurface R)) ((normalizationSurfaceEquiv R).symm x)) :=
  rfl

/-- The conjugated permutations give the transported `Gamma` action on the normalized surface. -/
instance normalizedGammaMulAction
    {R : Type u} [CommRing R] [Invertible (3 : R)] :
    MulAction (Gamma R) (NormalizedMarkoffSurface R) where
  smul g x := normalizedGammaPerm R g x
  one_smul x := by
    change normalizedGammaPerm R 1 x = x
    change normalizationSurfaceEquiv R ((normalizationSurfaceEquiv R).symm x) = x
    exact (normalizationSurfaceEquiv R).apply_symm_apply x
  mul_smul g h x := by
    change normalizedGammaPerm R (g * h) x =
      normalizedGammaPerm R g (normalizedGammaPerm R h x)
    change normalizationSurfaceEquiv R
        (((g * h : Gamma R) : Equiv.Perm (MarkoffSurface R))
          ((normalizationSurfaceEquiv R).symm x)) =
      normalizationSurfaceEquiv R
        ((g : Equiv.Perm (MarkoffSurface R)) ((normalizationSurfaceEquiv R).symm
          (normalizationSurfaceEquiv R
            ((h : Equiv.Perm (MarkoffSurface R))
              ((normalizationSurfaceEquiv R).symm x)))))
    rw [(normalizationSurfaceEquiv R).symm_apply_apply]
    rfl

@[simp]
theorem normalizedGamma_smul_eq_perm
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (g : Gamma R) (x : NormalizedMarkoffSurface R) :
    g • x = normalizedGammaPerm R g x :=
  rfl

/-- The orbit of a normalized point under the transported `Gamma` action. -/
def normalizedGammaOrbit
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) : Set (NormalizedMarkoffSurface R) :=
  MulAction.orbit (Gamma R) x

/-- Two normalized points are in the same component exactly when their inverse normalizations are
in one original-coordinate `Gamma`-orbit. -/
def SameNormalizedComponent {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x y : NormalizedMarkoffSurface R) : Prop :=
  SameComponent ((normalizationSurfaceEquiv R).symm x)
    ((normalizationSurfaceEquiv R).symm y)

/-- Orbit membership in normalized coordinates is witnessed by a conjugated element of `Gamma`. -/
theorem sameNormalizedComponent_iff_exists_gamma
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x y : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x y ↔ ∃ g : Gamma R, normalizedGammaPerm R g x = y := by
  rw [SameNormalizedComponent, sameComponent_iff_exists]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [normalizedGammaPerm_apply]
    change (g : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        (normalizationSurfaceEquiv R).symm y at hg
    rw [hg, (normalizationSurfaceEquiv R).apply_symm_apply]
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [normalizedGammaPerm_apply] at hg
    change (g : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        (normalizationSurfaceEquiv R).symm y
    apply (normalizationSurfaceEquiv R).injective
    simpa using hg

/-- The transported component relation agrees with the orbit of the transported action. -/
theorem sameNormalizedComponent_iff_mem_normalizedGammaOrbit
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x y : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x y ↔ y ∈ normalizedGammaOrbit x := by
  rw [sameNormalizedComponent_iff_exists_gamma]
  rfl

@[refl]
theorem sameNormalizedComponent_refl
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x x :=
  sameComponent_refl _

@[symm]
theorem sameNormalizedComponent_symm
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    {x y : NormalizedMarkoffSurface R}
    (h : SameNormalizedComponent x y) :
    SameNormalizedComponent y x :=
  sameComponent_symm h

@[trans]
theorem sameNormalizedComponent_trans
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    {x y z : NormalizedMarkoffSurface R}
    (hxy : SameNormalizedComponent x y) (hyz : SameNormalizedComponent y z) :
    SameNormalizedComponent x z :=
  sameComponent_trans hxy hyz

/-- Exchange the first two normalized coordinates on the normalized surface. -/
def normalizedSwap12Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedSwap12 x.1, by
    change normalizedPolynomial (normalizedSwap12 x.1) = 0
    rw [normalizedPolynomial_swap12]
    exact x.property⟩

/-- Exchange the last two normalized coordinates on the normalized surface. -/
def normalizedSwap23Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedSwap23 x.1, by
    change normalizedPolynomial (normalizedSwap23 x.1) = 0
    rw [normalizedPolynomial_swap23]
    exact x.property⟩

@[simp]
theorem coe_normalizedSwap12Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) :
    ((normalizedSwap12Surface x : NormalizedMarkoffSurface R) : NormalizedPoint R) =
      normalizedSwap12 x :=
  rfl

@[simp]
theorem coe_normalizedSwap23Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) :
    ((normalizedSwap23Surface x : NormalizedMarkoffSurface R) : NormalizedPoint R) =
      normalizedSwap23 x :=
  rfl

/-- The first normalized transposition is transported from the original surface. -/
theorem normalizedSwap12Surface_eq_transport
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    normalizedSwap12Surface x =
      normalizationSurfaceEquiv R
        (swap12SurfacePerm R ((normalizationSurfaceEquiv R).symm x)) := by
  apply Subtype.ext
  change normalizedSwap12 x =
    toNormalized (swap12 ((normalizationSurfaceEquiv R).symm x : Point R))
  rw [toNormalized_swap12]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

/-- The second normalized transposition is transported from the original surface. -/
theorem normalizedSwap23Surface_eq_transport
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    normalizedSwap23Surface x =
      normalizationSurfaceEquiv R
        (swap23SurfacePerm R ((normalizationSurfaceEquiv R).symm x)) := by
  apply Subtype.ext
  change normalizedSwap23 x =
    toNormalized (swap23 ((normalizationSurfaceEquiv R).symm x : Point R))
  rw [toNormalized_swap23]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

/-- The transported first coordinate transposition is the normalized swap. -/
@[simp]
theorem gammaSwap12_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    gammaSwap12 R • x = normalizedSwap12Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaSwap12 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        swap12SurfacePerm R ((normalizationSurfaceEquiv R).symm x) by
    exact gammaSwap12_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  exact (normalizedSwap12Surface_eq_transport x).symm

/-- The transported second coordinate transposition is the normalized swap. -/
@[simp]
theorem gammaSwap23_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    gammaSwap23 R • x = normalizedSwap23Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaSwap23 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        swap23SurfacePerm R ((normalizationSurfaceEquiv R).symm x) by
    exact gammaSwap23_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  exact (normalizedSwap23Surface_eq_transport x).symm

/-- Swapping the first two normalized coordinates stays in the same component. -/
theorem sameNormalizedComponent_swap12Surface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x (normalizedSwap12Surface x) :=
  (sameNormalizedComponent_iff_exists_gamma x _).2
    ⟨gammaSwap12 R, by simpa using gammaSwap12_smul_normalizedSurface x⟩

/-- Swapping the last two normalized coordinates stays in the same component. -/
theorem sameNormalizedComponent_swap23Surface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x (normalizedSwap23Surface x) :=
  (sameNormalizedComponent_iff_exists_gamma x _).2
    ⟨gammaSwap23 R, by simpa using gammaSwap23_smul_normalizedSurface x⟩

/-- The fundamental normalized rotation, restricted to the normalized surface. -/
def normalizedRotate1Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedRotate1 x.1, (isNormalizedMarkoff_rotate1 x.1).2 x.property⟩

@[simp]
theorem coe_normalizedRotate1Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) :
    ((normalizedRotate1Surface x : NormalizedMarkoffSurface R) : NormalizedPoint R) =
      normalizedRotate1 x :=
  rfl

/-- Normalized rotation is the normalization of the original surface rotation. -/
theorem normalizedRotate1Surface_eq_transport
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    normalizedRotate1Surface x =
      normalizationSurfaceEquiv R
        (rotate1Surface ((normalizationSurfaceEquiv R).symm x)) := by
  apply Subtype.ext
  change normalizedRotate1 x =
    toNormalized (rotate1 ((normalizationSurfaceEquiv R).symm x : Point R))
  rw [toNormalized_rotate1]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

/-- The transported explicit rotation element acts by normalized rotation. -/
@[simp]
theorem gammaRotate1_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    gammaRotate1 R • x = normalizedRotate1Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaRotate1 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        rotate1Surface ((normalizationSurfaceEquiv R).symm x) by
    exact gammaRotate1_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  exact (normalizedRotate1Surface_eq_transport x).symm

/-- One normalized rotation stays in the transported Markoff component. -/
theorem sameNormalizedComponent_rotate1Surface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) :
    SameNormalizedComponent x (normalizedRotate1Surface x) := by
  rw [SameNormalizedComponent, normalizedRotate1Surface_eq_transport]
  simpa using sameComponent_rotate1Surface ((normalizationSurfaceEquiv R).symm x)

/-- Every natural iterate of the normalized rotation stays in the same transported component. -/
theorem sameNormalizedComponent_iterate_normalizedRotate1Surface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) (n : ℕ) :
    SameNormalizedComponent x ((normalizedRotate1Surface^[n]) x) := by
  induction n with
  | zero => exact sameNormalizedComponent_refl x
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sameNormalizedComponent_trans ih
        (sameNormalizedComponent_rotate1Surface ((normalizedRotate1Surface^[n]) x))

/-- In particular, every positive iterate stays in the same transported component. -/
theorem sameNormalizedComponent_positive_iterate_normalizedRotate1Surface
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : NormalizedMarkoffSurface R) (n : ℕ) (_hn : 0 < n) :
    SameNormalizedComponent x ((normalizedRotate1Surface^[n]) x) :=
  sameNormalizedComponent_iterate_normalizedRotate1Surface x n

end BGS.Markoff
