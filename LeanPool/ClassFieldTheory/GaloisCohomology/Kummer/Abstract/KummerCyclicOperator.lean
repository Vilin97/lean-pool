/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.NormKernelVanishing

/-! # Kummer Cyclic Operator -/
namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: the cyclic
  abstract-operator step

This file isolates the finite cyclic step in the proof of the finite abelian Kummer decomposition.
It does not claim the full Kummer correspondence.  In additive notation, we
use a fixed kernel element `xi` of an equivariant operator `wp`, of order
`n`.  If the cyclic Galois group is killed by `n`, the vanishing of `H⁻¹`
produces one element `a` such that `wp a` is fixed and `a` has trivial
stabilizer.  This is the abstract analogue of the construction
`a^σ⁻¹ = ζ` and hence the single-radical generation step.
-/

noncomputable section

open CategoryTheory

/-- Stabilizer for the action carried by a representation.  We keep it
explicit because a `Representation` does not install its action as a global
`MulAction` instance on the underlying module. -/
def representationStabilizer {Q : IntegralRepGroupType} [Group Q]
    (B : Rep ℤ Q) (a : B.V) : Subgroup Q := by
  letI : Module ℤ B.V := B.hV2
  exact
    { carrier := {q | B.ρ q a = a}
      one_mem' := by
        change B.ρ (1 : Q) a = a
        exact congrArg (fun f : Module.End ℤ B.V => f a) (map_one B.ρ)
      mul_mem' := by
        intro q r hq hr
        change B.ρ (q * r) a = a
        rw [map_mul]
        change B.ρ q (B.ρ r a) = a
        rw [hr, hq]
      inv_mem' := by
        intro q hq
        change B.ρ q⁻¹ a = a
        calc
          B.ρ q⁻¹ a = B.ρ q⁻¹ (B.ρ q a) := congrArg (B.ρ q⁻¹) hq.symm
          _ = a := Representation.inv_self_apply B.ρ q a }

/-- The cohomological core of the finite cyclic case of the finite abelian Kummer decomposition.

The two conclusions say that `wp a` belongs to the base fixed module and
that the orbit of `a` has the full size of `Q`.  No radical element or
generation assertion is assumed. -/
theorem cyclic_single_radical_of_tateHMinusOne_isZero
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology B (-1)))
    (wp : B ⟶ B) (n : ℕ+) (xi : B.V)
    (hxi_order : addOrderOf xi = (n : ℕ))
    (hxi_kernel : wp.hom xi = 0)
    (hxi_fixed : ∀ q : Q, B.ρ q xi = xi)
    (hexponent : ∀ q : Q, q ^ (n : ℕ) = 1) :
    ∃ a : B.V,
      (∀ q : Q, B.ρ q (wp.hom a) = wp.hom a) ∧
      representationStabilizer B a = ⊥ := by
  let d := Fintype.card Q
  let eta : B.V := ((n : ℕ) / d) • xi
  have hd_pos : 0 < d := Fintype.card_pos
  have hn_pos : 0 < (n : ℕ) := n.pos
  have hg_order : orderOf g = d :=
    by simpa [d] using orderOf_eq_card_of_forall_mem_zpowers hg
  have hdegree : d ∣ (n : ℕ) := by
    rw [← hg_order]
    exact orderOf_dvd_of_pow_eq_one (hexponent g)
  have hquot_pos : 0 < (n : ℕ) / d :=
    Nat.div_pos (Nat.le_of_dvd hn_pos hdegree) hd_pos
  have hquot_dvd : (n : ℕ) / d ∣ addOrderOf xi := by
    rw [hxi_order]
    exact Nat.div_dvd_of_dvd hdegree
  have heta_order : addOrderOf eta = d := by
    calc
      addOrderOf eta = addOrderOf xi / ((n : ℕ) / d) :=
        addOrderOf_nsmul_of_dvd hquot_pos.ne' hquot_dvd
      _ = (n : ℕ) / ((n : ℕ) / d) := by rw [hxi_order]
      _ = d := Nat.div_div_self hdegree hn_pos.ne'
  have heta_fixed (q : Q) : B.ρ q eta = eta := by
    simp only [eta, map_nsmul, hxi_fixed]
  have heta_kernel : wp.hom eta = 0 := by
    simp only [eta, map_nsmul, hxi_kernel, smul_zero]
  have heta_norm : B.norm.hom eta = 0 := by
    have hnorm : B.norm.hom eta = d • eta := by
      simp [Rep.norm, Representation.norm, d, heta_fixed]
    rw [hnorm, ← heta_order]
    exact addOrderOf_nsmul_eq_zero eta
  obtain ⟨a, ha⟩ :=
    normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      B g hg hzero eta heta_norm
  have ha' : B.ρ g a = eta + a := by
    exact eq_add_of_sub_eq ha
  have hwp_g_fixed : B.ρ g (wp.hom a) = wp.hom a := by
    apply sub_eq_zero.mp
    calc
      B.ρ g (wp.hom a) - wp.hom a =
          wp.hom (B.ρ g a) - wp.hom a := by rw [Rep.hom_comm_apply]
      _ = wp.hom (B.ρ g a - a) := by rw [map_sub]
      _ = wp.hom eta := by rw [ha]
      _ = 0 := heta_kernel
  have hwp_fixed (q : Q) : B.ρ q (wp.hom a) = wp.hom a := by
    let H := representationStabilizer B (wp.hom a)
    have hg_mem : g ∈ H := hwp_g_fixed
    exact (Subgroup.zpowers_le.mpr hg_mem) (hg q)
  have horbit (i : ℕ) : B.ρ (g ^ i) a = i • eta + a := by
    induction i with
    | zero => simp
    | succ i hi =>
        rw [pow_succ', map_mul]
        change B.ρ g (B.ρ (g ^ i) a) = _
        rw [hi, map_add, map_nsmul, heta_fixed, ha']
        simp only [succ_nsmul]
        abel
  refine ⟨a, hwp_fixed, ?_⟩
  ext q
  constructor
  · intro hq
    have hq_fixed : B.ρ q a = a := hq
    obtain ⟨i, hi, _⟩ := IsCyclic.unique_zpow_zmod hg q
    have hi_smul : i.val • eta = 0 := by
      have := horbit i.val
      rw [← hi, hq_fixed] at this
      have hsub := congrArg (fun x : B.V => x - a) this
      simpa using hsub.symm
    have hd_dvd : d ∣ i.val := by
      rw [← heta_order]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hi_smul
    have hi_lt : i.val < d := i.val_lt
    have hi_zero : i.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hd_dvd hi_lt
    rw [hi, hi_zero, pow_zero]
    exact Subgroup.mem_bot.mpr rfl
  · intro hq
    rw [Subgroup.mem_bot] at hq
    subst q
    exact Subgroup.one_mem _

/-- Finite-cyclic, single-radical frontier of finite abelian Kummer theory, the finite abelian
Kummer decomposition,
now obtained from `SatisfiesCyclicNormKernelVanishing` itself.

Here `B` is the actual coefficient representation `A_L` attached to the
abstract cyclic extension.  The operator is stated on `B`; constructing it
functorially from a global operator on `A`, and assembling cyclic
subextensions into the full abelian Kummer extension, are deliberately not
claimed in this theorem. -/
theorem cyclicOperator_singleRadical_of_normKernelVanishing
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hAxiom : SatisfiesCyclicNormKernelVanishing A)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (wp : extensionFixedRepresentation A K L hLK hnormal ⟶
      extensionFixedRepresentation A K L hLK hnormal)
    (n : ℕ+) (xi : (extensionFixedRepresentation A K L hLK hnormal).V)
    (hxi_order : addOrderOf xi = (n : ℕ))
    (hxi_kernel : wp.hom xi = 0)
    (hxi_fixed : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      (extensionFixedRepresentation A K L hLK hnormal).ρ q xi = xi)
    (hexponent : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      q ^ (n : ℕ) = 1) :
    ∃ a : (extensionFixedRepresentation A K L hLK hnormal).V,
      (∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
        (extensionFixedRepresentation A K L hLK hnormal).ρ q (wp.hom a) = wp.hom a) ∧
      representationStabilizer (extensionFixedRepresentation A K L hLK hnormal) a = ⊥ := by
  let : Fintype (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  have hzero : Limits.IsZero
      (tateCohomology (extensionFixedRepresentation A K L hLK hnormal) (-1)) :=
    hAxiom K L hLK hnormal hfinite g hg
  apply cyclic_single_radical_of_tateHMinusOne_isZero
    (extensionFixedRepresentation A K L hLK hnormal) g hg hzero
    wp n xi hxi_order hxi_kernel hxi_fixed hexponent

end
end KummerTheory
