/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.NatConnectivity
import LeanPool.MarkoffModP.BGS.Markoff.Core.Statements

/-!
# Punctured finite-field transitivity and reduction surjectivity

The Markoff equation defines a functor on commutative semirings.  This file identifies the
finite-field transitivity statement used by the dynamical proof with the source-faithful
arithmetic statement that reduction from natural-number Markoff solutions is surjective.
-/

namespace BGS.Markoff

/-- Reduction from natural-number solutions, viewed in the existing ring-level surface. -/
def markoffReductionSurface (p : ℕ) :
    SemiringMarkoffSurface ℕ → MarkoffSurface (ZMod p) :=
  semiringMarkoffSurfaceEquiv (ZMod p) ∘ markoffReduction p

@[simp]
theorem markoffReductionSurface_origin (p : ℕ) :
    markoffReductionSurface p (semiringSurfaceOrigin ℕ) = surfaceOrigin (ZMod p) := by
  change semiringMarkoffSurfaceEquiv (ZMod p)
      (markoffReduction p (semiringSurfaceOrigin ℕ)) = surfaceOrigin (ZMod p)
  rw [markoffReduction_origin, semiringMarkoffSurfaceEquiv_origin]

@[simp]
theorem markoffReductionSurface_root (p : ℕ) :
    markoffReductionSurface p (semiringSurfaceRoot ℕ) = surfaceRoot (ZMod p) := by
  change semiringMarkoffSurfaceEquiv (ZMod p)
      (markoffReduction p (semiringSurfaceRoot ℕ)) = surfaceRoot (ZMod p)
  rw [markoffReduction_root, semiringMarkoffSurfaceEquiv_root]

private theorem natCoordinate_le_vietaProduct {a b c : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    a ≤ 3 * b * c := by
  by_cases ha : a = 0
  · simp [ha]
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    apply Nat.le_of_mul_le_mul_left _ haPos
    calc
      a * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by nlinarith
      _ = 3 * a * b * c := h
      _ = a * (3 * b * c) := by ring

@[simp]
theorem markoffReductionSurface_natVieta1 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReductionSurface p (natVieta1Surface x) =
      vieta1SurfacePerm (ZMod p) (markoffReductionSurface p x) := by
  have hle : x.1.x1 ≤ 3 * x.1.x2 * x.1.x3 :=
    natCoordinate_le_vietaProduct x.2
  apply Subtype.ext
  ext
  · change ((3 * x.1.x2 * x.1.x3 - x.1.x1 : ℕ) : ZMod p) =
      3 * (x.1.x2 : ZMod p) * (x.1.x3 : ZMod p) - (x.1.x1 : ZMod p)
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  · rfl
  · rfl

@[simp]
theorem markoffReductionSurface_natVieta2 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReductionSurface p (natVieta2Surface x) =
      vieta2SurfacePerm (ZMod p) (markoffReductionSurface p x) := by
  have hreorder : x.1.x2 ^ 2 + x.1.x1 ^ 2 + x.1.x3 ^ 2 =
      3 * x.1.x2 * x.1.x1 * x.1.x3 := by
    simpa [IsSemiringMarkoff, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2
  have hle : x.1.x2 ≤ 3 * x.1.x1 * x.1.x3 :=
    natCoordinate_le_vietaProduct hreorder
  apply Subtype.ext
  ext
  · rfl
  · change ((3 * x.1.x1 * x.1.x3 - x.1.x2 : ℕ) : ZMod p) =
      3 * (x.1.x1 : ZMod p) * (x.1.x3 : ZMod p) - (x.1.x2 : ZMod p)
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  · rfl

@[simp]
theorem markoffReductionSurface_natVieta3 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReductionSurface p (natVieta3Surface x) =
      vieta3SurfacePerm (ZMod p) (markoffReductionSurface p x) := by
  have hreorder : x.1.x3 ^ 2 + x.1.x1 ^ 2 + x.1.x2 ^ 2 =
      3 * x.1.x3 * x.1.x1 * x.1.x2 := by
    simpa [IsSemiringMarkoff, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2
  have hle : x.1.x3 ≤ 3 * x.1.x1 * x.1.x2 :=
    natCoordinate_le_vietaProduct hreorder
  apply Subtype.ext
  ext
  · rfl
  · rfl
  · change ((3 * x.1.x1 * x.1.x2 - x.1.x3 : ℕ) : ZMod p) =
      3 * (x.1.x1 : ZMod p) * (x.1.x2 : ZMod p) - (x.1.x3 : ZMod p)
    rw [Nat.cast_sub hle]
    push_cast
    rfl

@[simp]
theorem markoffReductionSurface_natSwap12 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReductionSurface p (natSwap12Surface x) =
      swap12SurfacePerm (ZMod p) (markoffReductionSurface p x) := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem markoffReductionSurface_natSwap23 (p : ℕ) (x : SemiringMarkoffSurface ℕ) :
    markoffReductionSurface p (natSwap23Surface x) =
      swap23SurfacePerm (ZMod p) (markoffReductionSurface p x) := by
  apply Subtype.ext
  ext <;> rfl

/-- Every word in the finite-field Markoff group has a word in the natural Markoff group whose
action commutes with reduction. -/
theorem exists_naturalGamma_lift (p : ℕ) (g : Gamma (ZMod p)) :
    ∃ h : NaturalGamma, ∀ x : SemiringMarkoffSurface ℕ,
      markoffReductionSurface p (h • x) = g • markoffReductionSurface p x := by
  let motive : ∀ q : Equiv.Perm (MarkoffSurface (ZMod p)),
      q ∈ Subgroup.closure (gammaGenerators (ZMod p)) → Prop :=
    fun q hq ↦ ∃ h : NaturalGamma, ∀ x : SemiringMarkoffSurface ℕ,
      markoffReductionSurface p (h • x) =
        (⟨q, hq⟩ : Gamma (ZMod p)) • markoffReductionSurface p x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [gammaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · refine ⟨⟨natVieta1SurfaceEquiv, natVieta1SurfaceEquiv_mem_NaturalGamma⟩, fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta1 p x
    · refine ⟨⟨natVieta2SurfaceEquiv, natVieta2SurfaceEquiv_mem_NaturalGamma⟩, fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta2 p x
    · refine ⟨⟨natVieta3SurfaceEquiv, natVieta3SurfaceEquiv_mem_NaturalGamma⟩, fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta3 p x
    · refine ⟨⟨natSwap12SurfaceEquiv, natSwap12SurfaceEquiv_mem_NaturalGamma⟩, fun x ↦ ?_⟩
      exact markoffReductionSurface_natSwap12 p x
    · refine ⟨⟨natSwap23SurfaceEquiv, natSwap23SurfaceEquiv_mem_NaturalGamma⟩, fun x ↦ ?_⟩
      exact markoffReductionSurface_natSwap23 p x
  · refine ⟨1, fun x ↦ ?_⟩
    change markoffReductionSurface p ((1 : NaturalGamma) • x) =
      (1 : Gamma (ZMod p)) • markoffReductionSurface p x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qNat, hqNat⟩ := hqLift
    obtain ⟨rNat, hrNat⟩ := hrLift
    refine ⟨qNat * rNat, fun x ↦ ?_⟩
    change markoffReductionSurface p ((qNat * rNat) • x) =
      ((⟨q, hq⟩ : Gamma (ZMod p)) * (⟨r, hr⟩ : Gamma (ZMod p))) •
        markoffReductionSurface p x
    rw [mul_smul, mul_smul, hqNat, hrNat]
  · intro q hq hqLift
    obtain ⟨qNat, hqNat⟩ := hqLift
    refine ⟨qNat⁻¹, fun x ↦ ?_⟩
    change markoffReductionSurface p (qNat⁻¹ • x) =
      (⟨q, hq⟩ : Gamma (ZMod p))⁻¹ • markoffReductionSurface p x
    have h := congrArg (fun y ↦ (⟨q, hq⟩ : Gamma (ZMod p))⁻¹ • y)
      (hqNat (qNat⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- Every word in the natural Markoff group reduces to a word in the finite-field Markoff group. -/
theorem exists_gamma_reduction_of_naturalGamma (p : ℕ) (h : NaturalGamma) :
    ∃ g : Gamma (ZMod p), ∀ x : SemiringMarkoffSurface ℕ,
      markoffReductionSurface p (h • x) = g • markoffReductionSurface p x := by
  let motive : ∀ q : Equiv.Perm (SemiringMarkoffSurface ℕ),
      q ∈ Subgroup.closure naturalGammaGenerators → Prop :=
    fun q hq ↦ ∃ g : Gamma (ZMod p), ∀ x : SemiringMarkoffSurface ℕ,
      markoffReductionSurface p ((⟨q, hq⟩ : NaturalGamma) • x) =
        g • markoffReductionSurface p x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [naturalGammaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · refine ⟨gammaVieta1 (ZMod p), fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta1 p x
    · refine ⟨gammaVieta2 (ZMod p), fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta2 p x
    · refine ⟨gammaVieta3 (ZMod p), fun x ↦ ?_⟩
      exact markoffReductionSurface_natVieta3 p x
    · refine ⟨gammaSwap12 (ZMod p), fun x ↦ ?_⟩
      exact markoffReductionSurface_natSwap12 p x
    · refine ⟨gammaSwap23 (ZMod p), fun x ↦ ?_⟩
      exact markoffReductionSurface_natSwap23 p x
  · refine ⟨1, fun x ↦ ?_⟩
    change markoffReductionSurface p ((1 : NaturalGamma) • x) =
      (1 : Gamma (ZMod p)) • markoffReductionSurface p x
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qMod, hqMod⟩ := hqLift
    obtain ⟨rMod, hrMod⟩ := hrLift
    refine ⟨qMod * rMod, fun x ↦ ?_⟩
    change markoffReductionSurface p
        (((⟨q, hq⟩ : NaturalGamma) * (⟨r, hr⟩ : NaturalGamma)) • x) =
      (qMod * rMod) • markoffReductionSurface p x
    rw [mul_smul, mul_smul, hqMod, hrMod]
  · intro q hq hqLift
    obtain ⟨qMod, hqMod⟩ := hqLift
    refine ⟨qMod⁻¹, fun x ↦ ?_⟩
    change markoffReductionSurface p ((⟨q, hq⟩ : NaturalGamma)⁻¹ • x) =
      qMod⁻¹ • markoffReductionSurface p x
    have hred := congrArg (fun y ↦ qMod⁻¹ • y)
      (hqMod ((⟨q, hq⟩ : NaturalGamma)⁻¹ • x))
    simpa [mul_smul] using hred.symm

/-- Natural Markoff connectivity descends to finite-field Markoff connectivity. -/
theorem sameComponent_markoffReductionSurface_of_sameNatMarkoffComponent
    (p : ℕ) {x y : SemiringMarkoffSurface ℕ}
    (hxy : SameNatMarkoffComponent x y) :
    SameComponent (markoffReductionSurface p x) (markoffReductionSurface p y) := by
  unfold SameNatMarkoffComponent at hxy
  rw [MulAction.mem_orbit_iff] at hxy
  obtain ⟨h, rfl⟩ := hxy
  obtain ⟨g, hg⟩ := exists_gamma_reduction_of_naturalGamma p h
  exact (sameComponent_iff_exists _ _).2 ⟨g, (hg x).symm⟩

@[simp]
theorem surfaceRoot_ne_surfaceOrigin (R : Type*) [CommRing R] [Nontrivial R] :
    surfaceRoot R ≠ surfaceOrigin R := by
  intro h
  have hfirst := congrArg (fun x : MarkoffSurface R ↦ x.1.x1) h
  change (1 : R) = 0 at hfirst
  exact one_ne_zero hfirst

/-- Finite-field transitivity implies surjectivity of reduction from natural-number solutions. -/
theorem markoffReduction_surjective_of_puncturedMarkoffTransitiveAt
    (p : ℕ) (hp : p.Prime) (htransitive : PuncturedMarkoffTransitiveAt p hp) :
    Function.Surjective (markoffReduction p) := by
  let : Fact p.Prime := ⟨hp⟩
  change ∀ x y : PuncturedMarkoffSurface (ZMod p),
    ∃ g : Gamma (ZMod p), g • x = y at htransitive
  intro y
  let ySurface : MarkoffSurface (ZMod p) := semiringMarkoffSurfaceEquiv (ZMod p) y
  by_cases hy : ySurface = surfaceOrigin (ZMod p)
  · refine ⟨semiringSurfaceOrigin ℕ, ?_⟩
    apply (semiringMarkoffSurfaceEquiv (ZMod p)).injective
    change markoffReductionSurface p (semiringSurfaceOrigin ℕ) = ySurface
    rw [markoffReductionSurface_origin, hy]
  · let root : PuncturedMarkoffSurface (ZMod p) :=
      ⟨surfaceRoot (ZMod p), surfaceRoot_ne_surfaceOrigin (ZMod p)⟩
    let target : PuncturedMarkoffSurface (ZMod p) := ⟨ySurface, hy⟩
    obtain ⟨g, hg⟩ := htransitive root target
    obtain ⟨h, hh⟩ := exists_naturalGamma_lift p g
    refine ⟨h • semiringSurfaceRoot ℕ, ?_⟩
    apply (semiringMarkoffSurfaceEquiv (ZMod p)).injective
    change markoffReductionSurface p (h • semiringSurfaceRoot ℕ) = ySurface
    calc
      markoffReductionSurface p (h • semiringSurfaceRoot ℕ) =
          g • markoffReductionSurface p (semiringSurfaceRoot ℕ) :=
        hh (semiringSurfaceRoot ℕ)
      _ = g • surfaceRoot (ZMod p) := by rw [markoffReductionSurface_root]
      _ = ySurface := congrArg Subtype.val hg

/-- Surjectivity of natural-number reduction implies finite-field transitivity.  The classical
connectivity of nonzero natural Markoff solutions is the essential input in this direction. -/
theorem puncturedMarkoffTransitiveAt_of_markoffReduction_surjective
    (p : ℕ) (hp : p.Prime) (hsurjective : Function.Surjective (markoffReduction p)) :
    PuncturedMarkoffTransitiveAt p hp := by
  let : Fact p.Prime := ⟨hp⟩
  change ∀ x y : PuncturedMarkoffSurface (ZMod p),
    ∃ g : Gamma (ZMod p), g • x = y
  intro x y
  let xSemiring : SemiringMarkoffSurface (ZMod p) :=
    (semiringMarkoffSurfaceEquiv (ZMod p)).symm x.1
  let ySemiring : SemiringMarkoffSurface (ZMod p) :=
    (semiringMarkoffSurfaceEquiv (ZMod p)).symm y.1
  obtain ⟨xNat, hxNat⟩ := hsurjective xSemiring
  obtain ⟨yNat, hyNat⟩ := hsurjective ySemiring
  have hxSurface : markoffReductionSurface p xNat = x.1 := by
    change semiringMarkoffSurfaceEquiv (ZMod p) (markoffReduction p xNat) = x.1
    rw [hxNat, Equiv.apply_symm_apply]
  have hySurface : markoffReductionSurface p yNat = y.1 := by
    change semiringMarkoffSurfaceEquiv (ZMod p) (markoffReduction p yNat) = y.1
    rw [hyNat, Equiv.apply_symm_apply]
  have hxNatNe : xNat ≠ semiringSurfaceOrigin ℕ := by
    intro hxOrigin
    subst xNat
    rw [markoffReductionSurface_origin] at hxSurface
    exact x.2 hxSurface.symm
  have hyNatNe : yNat ≠ semiringSurfaceOrigin ℕ := by
    intro hyOrigin
    subst yNat
    rw [markoffReductionSurface_origin] at hySurface
    exact y.2 hySurface.symm
  have hxNatural : SameNatMarkoffComponent (semiringSurfaceRoot ℕ) xNat :=
    (natMarkoff_eq_origin_or_sameComponent_root xNat).resolve_left hxNatNe
  have hyNatural : SameNatMarkoffComponent (semiringSurfaceRoot ℕ) yNat :=
    (natMarkoff_eq_origin_or_sameComponent_root yNat).resolve_left hyNatNe
  have hxComponent : SameComponent (surfaceRoot (ZMod p)) x.1 := by
    simpa only [markoffReductionSurface_root, hxSurface] using
      sameComponent_markoffReductionSurface_of_sameNatMarkoffComponent p hxNatural
  have hyComponent : SameComponent (surfaceRoot (ZMod p)) y.1 := by
    simpa only [markoffReductionSurface_root, hySurface] using
      sameComponent_markoffReductionSurface_of_sameNatMarkoffComponent p hyNatural
  have hxy : SameComponent x.1 y.1 :=
    sameComponent_trans (sameComponent_symm hxComponent) hyComponent
  obtain ⟨g, hg⟩ := (sameComponent_iff_exists x.1 y.1).1 hxy
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

/-- The source-faithful reduction statement is equivalent to the finite-field transitivity
statement used by the BGS dynamical proof. -/
theorem puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective
    (p : ℕ) (hp : p.Prime) :
    PuncturedMarkoffTransitiveAt p hp ↔ Function.Surjective (markoffReduction p) :=
  ⟨markoffReduction_surjective_of_puncturedMarkoffTransitiveAt p hp,
    puncturedMarkoffTransitiveAt_of_markoffReduction_surjective p hp⟩

/-- For prime moduli, punctured finite-field transitivity is equivalent to strong
approximation.  Natural Markoff connectivity is the essential input from right to left. -/
theorem puncturedMarkoffTransitiveAt_iff_strongApproximationAt
    (p : ℕ) (hp : p.Prime) :
    PuncturedMarkoffTransitiveAt p hp ↔ StrongApproximationAt p :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective p hp).trans
    (strongApproximationAt_iff_markoffReduction_surjective p).symm

end BGS.Markoff
