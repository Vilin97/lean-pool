/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm
public import Mathlib.Dynamics.BirkhoffSum.Basic

/-! # Universal Norm Descent -/

@[expose] public section
universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Universal norm descent

This module contains the representation-theoretic lifting and correction
calculation used by the abstract reciprocity construction, together with
the norm, action, and iterate identities it requires.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- The norm over a finite normal subgroup commutes with every ambient
group action.  This is the equivariance used when the construction applies the norm
to equation `(*)`. -/
private theorem restricted_norm_action
    {R : IntegralRepGroupType} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (r : R) (x : B.V) :
    (∑ h : H, B.ρ h.1 (B.ρ r x)) =
      B.ρ r (∑ h : H, B.ρ h.1 x) := by
  rw [map_sum]
  let e : H ≃ H := (MulAut.conjNormal r).symm.toEquiv
  calc
    (∑ h : H, B.ρ h.1 (B.ρ r x)) =
        ∑ h : H, B.ρ r (B.ρ (e h).1 x) := by
      apply Finset.sum_congr rfl
      intro h _
      have he : (e h).1 = r⁻¹ * h.1 * r := by
        exact MulAut.conjNormal_symm_apply r h
      calc
        B.ρ h.1 (B.ρ r x) = B.ρ (h.1 * r) x := by
          rw [map_mul]
          rfl
        _ = B.ρ (r * (e h).1) x := by
          rw [he]
          simp [mul_assoc]
        _ = B.ρ r (B.ρ (e h).1 x) := by
          rw [map_mul]
          rfl
    _ = ∑ h : H, B.ρ r (B.ρ h.1 x) := by
      exact e.sum_comp (fun h : H => B.ρ r (B.ρ h.1 x))

private theorem restricted_rep_norm_action
    {R : IntegralRepGroupType} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (r : R) (x : B.V) :
    let U : Rep ℤ H := Rep.res H.subtype B
    U.norm.hom (B.ρ r x) = B.ρ r (U.norm.hom x) := by
  let U : Rep ℤ H := Rep.res H.subtype B
  simpa [Rep.norm, Representation.norm] using
    restricted_norm_action H B r x

/-- Transport the ordinary conjugation action back to a field stabilized
by that conjugation. -/
noncomputable def conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a

private theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

private theorem relativeNorm_transport_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ extensionSubgroup F' E' hE'F')]
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) : B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') : B.V) := by
  cases hF
  cases hE
  rfl

/-- The conjugation-stable action agrees with its ambient action after coercion. -/
@[simp]
theorem conjugateStableAction_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1 := by
  exact transport_fixed_coe B _ F hF _

/-- Relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
theorem relativeNorm_conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a) := by
  let hConj := conjugateClosedSubgroup_mono hEF s
  let : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup F s)
        (conjugateClosedSubgroup E s) hConj) :=
    finite_conjugateExtension F E hEF s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a) :
        ambientFixedAddSubgroup B F) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a) :
            ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := by
      exact relativeNorm_transport_coe B
        (conjugateClosedSubgroup F s) (conjugateClosedSubgroup E s) F E
        hF hE hConj hEF (conjugateFixedElement B E s a)
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B F) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm

/-- The cohomological calculation in the first half of the universal norm-descent lemma.

The hypothesis `hstar` is precisely equation `(*)`: it says that
the class of `u` in coinvariants is fixed by `φ`.  The conclusion is not
assumed: `H⁰=0` first produces the barred lifts, and `H⁻¹=0` then produces
the correction term `y` appearing. -/
theorem universalNormDescent_cyclic_lift_and_correction
    {R : IntegralRepGroupType} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (g : H) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (hzero0 :
      let U : Rep ℤ H := Rep.res H.subtype B
      Limits.IsZero (tateCohomology U 0))
    (hzeroMinusOne :
      let U : Rep ℤ H := Rep.res H.subtype B
      Limits.IsZero (tateCohomology U (-1)))
    {ι : Type v} (s : Finset ι) (φ : R) (τ : ι → R)
    (u : B.V) (uᵢ : ι → B.V)
    (huFixed : ∀ q : H, B.ρ q.1 u = u)
    (huᵢFixed : ∀ (i : ι) (q : H), B.ρ q.1 (uᵢ i) = uᵢ i)
    (hstar : B.ρ φ u - u =
      ∑ i ∈ s, (B.ρ (τ i) (uᵢ i) - uᵢ i)) :
    ∃ (uBar : B.V) (uBarᵢ : ι → B.V) (y : B.V),
      (∑ q : H, B.ρ q.1 uBar) = u ∧
      (∀ i, (∑ q : H, B.ρ q.1 (uBarᵢ i)) = uᵢ i) ∧
      B.ρ g.1 y - y =
        B.ρ φ uBar - uBar -
          ∑ i ∈ s, (B.ρ (τ i) (uBarᵢ i) - uBarᵢ i) := by
  let U : Rep ℤ H := Rep.res H.subtype B
  have huGenerator : U.ρ g u = u := huFixed g
  have huLift : ∃ z : B.V, U.norm.hom z = u :=
    exists_norm_eq_of_tateHZero_isZero U g hg hzero0 u huGenerator
  obtain ⟨uBar, huBar⟩ := huLift
  have huᵢGenerator (i : ι) : U.ρ g (uᵢ i) = uᵢ i := huᵢFixed i g
  have huᵢLift (i : ι) : ∃ z : B.V, U.norm.hom z = uᵢ i :=
    exists_norm_eq_of_tateHZero_isZero U g hg hzero0
      (uᵢ i) (huᵢGenerator i)
  choose uBarᵢ huBarᵢ using huᵢLift
  let delta : B.V :=
    B.ρ φ uBar - uBar -
      ∑ i ∈ s, (B.ρ (τ i) (uBarᵢ i) - uBarᵢ i)
  have hdeltaNorm : U.norm.hom delta = 0 := by
    calc
      U.norm.hom delta =
          U.norm.hom (B.ρ φ uBar) - U.norm.hom uBar -
            ∑ i ∈ s,
              (U.norm.hom (B.ρ (τ i) (uBarᵢ i)) -
                U.norm.hom (uBarᵢ i)) := by
        dsimp [delta]
        rw [map_sub, map_sub, map_sum]
        simp_rw [map_sub]
      _ = B.ρ φ u - u -
          ∑ i ∈ s, (B.ρ (τ i) (uᵢ i) - uᵢ i) := by
        rw [restricted_rep_norm_action H B φ uBar, huBar]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [restricted_rep_norm_action H B (τ i) (uBarᵢ i), huBarᵢ i]
      _ = 0 := by rw [hstar, sub_self]
  obtain ⟨y, hy⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      U g hg hzeroMinusOne delta hdeltaNorm
  refine ⟨uBar, uBarᵢ, y, ?_, ?_, ?_⟩
  · simpa [U, Rep.norm, Representation.norm] using huBar
  · intro i
    simpa [U, Rep.norm, Representation.norm] using huBarᵢ i
  · simpa [U, delta] using hy

/-- Enumerate the norm of a finite cyclic representation by the first
n powers of a specified generator. -/
theorem rep_norm_eq_generatorPowerSum
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x := by
  classical
  have horder : orderOf g = n := by
    calc
      orderOf g = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Fintype.card Q := Nat.card_eq_fintype_card
      _ = n := hcard
  let e : Fin n ≃ Q := Equiv.ofBijective (fun i => g ^ i.1) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hmod : i.1 ≡ j.1 [MOD orderOf g] :=
        (pow_eq_pow_iff_modEq).mp hij
      rw [horder] at hmod
      exact hmod.eq_of_lt_of_lt i.2 j.2
    · intro q
      have himage :
          Finset.image (fun i => g ^ i) (Finset.range n) = Finset.univ := by
        rw [← horder]
        exact IsCyclic.image_range_orderOf hg
      have hq : q ∈ Finset.image (fun i => g ^ i) (Finset.range n) := by
        rw [himage]
        simp
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiq⟩)
  have hsum : (∑ q : Q, B.ρ q x) =
      ∑ i : Fin n, B.ρ (g ^ i.1) x :=
    (e.sum_comp (fun q : Q => B.ρ q x)).symm
  simpa [Rep.norm, Representation.norm] using hsum

/-- Powers in a representation are the iterates of the corresponding
action map. -/
theorem rep_action_pow_eq_iterate {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  let : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

/-- Replace the generator action in the preceding norm formula by a
pointwise equal endomorphism and enumerate its iterates. -/
theorem rep_norm_eq_generatorIterateSum
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x := by
  rw [rep_norm_eq_generatorPowerSum B g hg n hcard x]
  apply Finset.sum_congr rfl
  intro i _
  rw [rep_action_pow_eq_iterate]
  exact congrFun (congrArg (fun h : B.V → B.V => h^[i.1]) (funext hf)) x

/-- Every nonnegative power fixes an element fixed by the original group
element. -/
theorem rep_action_pow_fixed {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    B.ρ (g ^ n) x = x := by
  rw [rep_action_pow_eq_iterate]
  exact Function.IsFixedPt.iterate hx n

end

end ClassFormation
