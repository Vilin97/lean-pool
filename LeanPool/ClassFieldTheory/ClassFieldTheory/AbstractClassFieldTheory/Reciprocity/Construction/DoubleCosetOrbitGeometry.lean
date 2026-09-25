/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
/-!
# Orbit quotients and double-coset geometry

This module contains the group-theoretic geometry used by the transfer formula:
orbit quotients of coset spaces, inversion of double cosets, transport along
surjective equivariant maps, and replacement of a cyclic subgroup by its
topological closure.  It has no class-formation or field-theoretic input.
-/

@[expose] public section

universe u

namespace ClassFormation

noncomputable section

open MulAction

/-- Orbits of `S` on `Q/H` are the double cosets `S \\ Q / H`.
This makes the indexing set in Mathlib's transfer formula literally the
double-coset set used by the abstract class-field construction. -/
noncomputable def orbitQuotientEquivDoubleCoset
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      DoubleCoset.Quotient (S : Set Q) (H : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun q => DoubleCoset.mk S H q.out) (by
      intro q₁ q₂ hq
      rw [orbitRel_apply, mem_orbit_iff] at hq
      obtain ⟨s, hs⟩ := hq
      symm
      apply DoubleCoset.eq.mpr
      have hcoset :
          (QuotientGroup.mk q₁.out : Q ⧸ H) =
            QuotientGroup.mk (s.1 * q₂.out) := by
        calc
          QuotientGroup.mk q₁.out = q₁ := Quotient.out_eq' q₁
          _ = s • q₂ := hs.symm
          _ = s • (QuotientGroup.mk q₂.out : Q ⧸ H) :=
            congrArg (s • ·) (Quotient.out_eq' q₂).symm
          _ = QuotientGroup.mk (s.1 * q₂.out) := rfl
      have hh : q₁.out⁻¹ * (s.1 * q₂.out) ∈ H :=
        QuotientGroup.eq.mp hcoset
      refine ⟨s.1, s.2, (q₁.out⁻¹ * (s.1 * q₂.out))⁻¹,
        H.inv_mem hh, ?_⟩
      simp [mul_assoc])
  invFun z := Quotient.liftOn' z
    (fun x => Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply Quotient.eq''.mpr
      rw [orbitRel_apply, mem_orbit_iff]
      refine ⟨⟨s⁻¹, S.inv_mem hs⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      simpa [mul_assoc] using hh)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro q
    change Quotient.mk'' (QuotientGroup.mk q.out : Q ⧸ H) = Quotient.mk'' q
    exact congrArg Quotient.mk'' (Quotient.out_eq' q)
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (Quotient.out
      (QuotientGroup.mk x : Q ⧸ H)) = DoubleCoset.mk S H x
    apply DoubleCoset.eq.mpr
    have hh : (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
      QuotientGroup.leftRel_apply.mp
        (Quotient.exact' (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
    exact ⟨1, S.one_mem,
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
      hh, by simp⟩

/-- The orbit-to-double-coset equivalence sends the orbit represented by
`x` to its double coset.  This exposes that the definition is independent
of the representative selected by `Quotient.out`. -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientEquivDoubleCoset S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      DoubleCoset.mk S H x := by
  change DoubleCoset.mk S H
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H)) =
    DoubleCoset.mk S H x
  apply DoubleCoset.eq.mpr
  have hh :
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact'
        (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
  exact ⟨1, S.one_mem,
    (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
    hh, by simp⟩

/-- The inverse double-coset equivalence sends a represented double coset
to the corresponding represented orbit. -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_symm_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    (orbitQuotientEquivDoubleCoset S H).symm (DoubleCoset.mk S H x) =
      Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H) :=
  rfl

/-- Inversion exchanges the two sides of a double-coset space. -/
noncomputable def doubleCosetInversionEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    DoubleCoset.Quotient (S : Set Q) (H : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q) (S : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H S x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply DoubleCoset.eq.mpr
      exact ⟨h⁻¹, H.inv_mem hh, s⁻¹, S.inv_mem hs,
        by simp [mul_assoc]⟩)
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk S H x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨h, hh, s, hs, rfl⟩ := hxy
      apply DoubleCoset.eq.mpr
      exact ⟨s⁻¹, S.inv_mem hs, h⁻¹, H.inv_mem hh,
        by simp [mul_assoc]⟩)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (x⁻¹)⁻¹ = DoubleCoset.mk S H x
    rw [inv_inv]
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk H S (x⁻¹)⁻¹ = DoubleCoset.mk H S x
    rw [inv_inv]

/-- Orbit sets on the two quotient spaces are exchanged by inversion.
This is the reindexing between the transfer and norm double-coset
decompositions in the proof of transfer--norm naturality. -/
noncomputable def orbitQuotientSwapEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      Quotient (orbitRel H (Q ⧸ S)) :=
  (orbitQuotientEquivDoubleCoset S H).trans
    ((doubleCosetInversionEquiv S H).trans
      (orbitQuotientEquivDoubleCoset H S).symm)

/-- The double-coset swap sends the orbit represented by `x` to the orbit
represented by `x⁻¹`; this proposition records that fact independently of
the representatives selected by `Quotient.out`. -/
@[simp]
theorem orbitQuotientSwapEquiv_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientSwapEquiv S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      Quotient.mk'' (QuotientGroup.mk x⁻¹ : Q ⧸ S) := by
  change (orbitQuotientEquivDoubleCoset H S).symm
      (doubleCosetInversionEquiv S H
        (orbitQuotientEquivDoubleCoset S H
          (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetInversionEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let u : Q := Quotient.out (QuotientGroup.mk x : Q ⧸ H)
  have hu : u⁻¹ * x ∈ H := by
    apply QuotientGroup.eq.mp
    exact Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)
  apply Quotient.sound'
  rw [orbitRel_apply, mem_orbit_iff]
  refine ⟨⟨u⁻¹ * x, hu⟩, ?_⟩
  change QuotientGroup.mk ((u⁻¹ * x) * x⁻¹) =
    (QuotientGroup.mk u⁻¹ : Q ⧸ S)
  simp [mul_assoc]

/-- A surjective homomorphism and an equivariant equivalence of the acted-on
sets induce an equivalence of orbit sets. -/
noncomputable def orbitQuotientEquivOfSurjectiveEquivariant
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) :
    Quotient (orbitRel M X) ≃ Quotient (orbitRel N Y) :=
  { toFun := Quotient.map' e (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨m, hm⟩ := hxy
      exact ⟨f m, (he m y).symm.trans (congrArg e hm)⟩)
    invFun := Quotient.map' e.symm (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨n, hn⟩ := hxy
      obtain ⟨m, rfl⟩ := hf n
      refine ⟨m, ?_⟩
      apply e.injective
      rw [he, e.apply_symm_apply, e.apply_symm_apply]
      exact hn)
    left_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change Quotient.mk'' (e.symm (e x)) = Quotient.mk'' x
      rw [e.symm_apply_apply]
    right_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro y
      change Quotient.mk'' (e (e.symm y)) = Quotient.mk'' y
      rw [e.apply_symm_apply] }

/-- The orbit-quotient equivalence sends a represented orbit to the image representative. -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (x : X) :
    orbitQuotientEquivOfSurjectiveEquivariant f hf e he
        (Quotient.mk'' x) = Quotient.mk'' (e x) :=
  rfl

/-- The inverse orbit-quotient equivalence lifts a representative to its source orbit. -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_symm_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (y : Y) :
    (orbitQuotientEquivOfSurjectiveEquivariant f hf e he).symm
        (Quotient.mk'' y) = Quotient.mk'' (e.symm y) :=
  rfl

/-- A group equivalence transports left cosets along the image of a
subgroup; no normality hypothesis is required. -/
noncomputable def leftCosetEquivOfMulEquiv
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) :
    Q ⧸ S ≃ R ⧸ S.map e.toMonoidHom where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact ⟨x⁻¹ * y, hxy, by simp⟩)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    obtain ⟨z, hz, heq⟩ := hxy
    have hzEq : e.symm (x⁻¹ * y) = z := by
      rw [← heq]
      simp
    have hxyEq : (e.symm x)⁻¹ * e.symm y = z := by
      calc
        (e.symm x)⁻¹ * e.symm y = e.symm (x⁻¹ * y) := by simp
        _ = z := hzEq
    rw [hxyEq]
    exact hz)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e.symm (e x)) = QuotientGroup.mk x
    rw [e.symm_apply_apply]
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e (e.symm x)) = QuotientGroup.mk x
    rw [e.apply_symm_apply]

/-- A multiplicative equivalence transports a left-coset representative as expected. -/
theorem leftCosetEquivOfMulEquiv_mk
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) (x : Q) :
    leftCosetEquivOfMulEquiv e S (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

/-- Closing a cyclic subgroup does not change its double cosets against a
closed finite-index subgroup.  This is the density/open-subgroup step which
passes from the algebraic powers of a Frobenius to its closed procyclic
subgroup in the classical argument. -/
theorem doubleCoset_closedCyclic_eq
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x y : Q) :
    DoubleCoset.mk H (Subgroup.zpowers g) x =
        DoubleCoset.mk H (Subgroup.zpowers g) y ↔
      DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x =
        DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup y := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  have hzC : Subgroup.zpowers g ≤ C := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.le_topologicalClosure _
  constructor
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, s, hs, hsxy⟩ := hxy
    exact ⟨h, hh, s, hzC hs, hsxy⟩
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, c, hc, rfl⟩ := hxy
    have hcclosure : c ∈ closure
        ((Subgroup.zpowers g : Subgroup Q) : Set Q) := by
      rw [Subgroup.zpowers_eq_closure]
      rw [← Subgroup.topologicalClosure_coe]
      change c ∈
        ((Subgroup.closure ({g} : Set Q)).topologicalClosure : Set Q) at hc
      exact hc
    let U : Set Q :=
      (fun s : Q => x * c * s⁻¹ * x⁻¹) ⁻¹' (H : Set Q)
    have hUopen : IsOpen U := by
      apply (((continuous_const.mul continuous_inv).mul
        continuous_const).isOpen_preimage (H : Set Q))
      exact H.isOpen_of_isClosed_of_finiteIndex hHclosed
    have hcU : c ∈ U := by
      change x * c * c⁻¹ * x⁻¹ ∈ H
      simp [mul_assoc]
    obtain ⟨s, hsU, hs⟩ :=
      (mem_closure_iff.mp hcclosure U hUopen hcU)
    have hsH : x * c * s⁻¹ * x⁻¹ ∈ H := hsU
    refine ⟨h * (x * c * s⁻¹ * x⁻¹), H.mul_mem hh hsH,
      s, hs, ?_⟩
    simp [mul_assoc]

/-- Double-coset equivalence induced by the preceding density argument. -/
noncomputable def doubleCosetClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    DoubleCoset.Quotient (H : Set Q) (Subgroup.zpowers g : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q)
        ((closedSubgroupGenerated ({g} : Set Q)).toSubgroup : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H
      (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mp
        (Quotient.sound' hxy))
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H (Subgroup.zpowers g) x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mpr
        (Quotient.sound' hxy))
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl

/-- On orbit sets, replacing the powers of a Frobenius by their closure is
an equivalence whenever the subgroup acting on the other side has finite
index and is closed. -/
noncomputable def orbitQuotientClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    Quotient (orbitRel H (Q ⧸ Subgroup.zpowers g)) ≃
      Quotient (orbitRel H
        (Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup)) :=
  (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)).trans
    ((doubleCosetClosedCyclicEquiv H hHclosed g).trans
      (orbitQuotientEquivDoubleCoset H
        (closedSubgroupGenerated ({g} : Set Q)).toSubgroup).symm)

/-- Passing from the powers of `g` to their closure preserves the orbit
represented by every literal group element. -/
@[simp]
theorem orbitQuotientClosedCyclicEquiv_mk
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x : Q) :
    orbitQuotientClosedCyclicEquiv H hHclosed g
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)) =
      Quotient.mk'' (QuotientGroup.mk x :
        Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup) := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  change (orbitQuotientEquivDoubleCoset H C).symm
      (doubleCosetClosedCyclicEquiv H hHclosed g
        (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)
          (Quotient.mk''
            (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetClosedCyclicEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let a := Quotient.out (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)
  have ha : a⁻¹ * x ∈ Subgroup.zpowers g :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' (Quotient.out_eq'
        (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))
  have haC : a⁻¹ * x ∈ C := by
    apply Subgroup.le_topologicalClosure _
    simpa [Subgroup.zpowers_eq_closure] using ha
  apply congrArg Quotient.mk''
  apply QuotientGroup.eq.mpr
  exact haC

end

end ClassFormation
