/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerFixedField

/-! # Kummer Abelian Assembly -/

@[expose] public section
namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: assembling cyclic radicals

This file connects elements produced in the invariant subtype `A_M` to the
ambient representation `A`.  A cyclic radical with trivial stabilizer in
`G_K / G_M` is fixed in the ambient module by exactly `G_M`.  Consequently,
a family of such radicals whose subgroups intersect in `G_L` generates the
abstract field `L` over `K`.
-/

noncomputable
section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Membership in `G_L`, regarded as a subgroup of `G_K`, is the same as
ambient membership in the closed subgroup `G_L`. -/
@[simp]
theorem mem_extensionSubgroup_iff
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) :
    k ∈ extensionSubgroup (G := G) K L hLK ↔ (k : G) ∈ L :=
  Iff.rfl

/-- The quotient action on an invariant subtype is the original ambient
action after choosing a representative in `G_K`. -/
theorem extensionFixedRepresentation_quotient_mk_apply_val
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K M hMK).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) :
    ((extensionFixedRepresentation A K M hMK hnormal).ρ
      ((QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k) a).1 =
      A.ρ k.1 a.1 := rfl

/-- If an element of `A_M` has trivial stabilizer under `G_K/G_M`, its
ambient value is fixed by `k : G_K` exactly when `k` belongs to `G_M`. -/
theorem extensionFixedRepresentation_val_fixed_iff_mem
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K M hMK).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (hstabilizer :
      representationStabilizer (extensionFixedRepresentation A K M hMK hnormal) a = ⊥)
    (k : K.toSubgroup) :
    A.ρ k.1 a.1 = a.1 ↔
      k ∈ extensionSubgroup (G := G) K M hMK := by
  constructor
  · intro hk
    have hq :
        (QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k ∈
          representationStabilizer
            (extensionFixedRepresentation A K M hMK hnormal) a := by
      change
        (extensionFixedRepresentation A K M hMK hnormal).ρ
          ((QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k) a = a
      apply Subtype.ext
      exact hk
    have hq_one :
        (QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k = 1 := by
      rw [← Subgroup.mem_bot]
      rwa [← hstabilizer]
    exact (QuotientGroup.eq_one_iff k).1 hq_one
  · intro hk
    exact a.2 ⟨k, hk⟩

/-- Quotient-fixedness of the descended global operator says precisely that
the ambient value `wp(a)` is fixed by `G_K`. -/
theorem extensionFixedEndomorphism_fixed_val
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K M hMK).Normal]
    (wp : A ⟶ A)
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (hfixed : ∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K M hMK,
      (extensionFixedRepresentation A K M hMK hnormal).ρ q
          ((extensionFixedEndomorphism A K M hMK wp).hom a) =
        (extensionFixedEndomorphism A K M hMK wp).hom a)
    (k : K.toSubgroup) :
    A.ρ k.1 (wp.hom a.1) = wp.hom a.1 := by
  have h := hfixed
    ((QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k)
  have hval := congrArg (fun x => x.1) h
  exact hval

/-- A family of faithful cyclic radicals generates `L` once the associated
subgroups intersect in `G_L`.  The generation conclusion is derived from
the radicals' stabilizers; it is not an input. -/
theorem closedSetFixingSubgroup_range_extensionFixed_eq
    (A : Rep ℤ G) (hcontinuous : IsContinuousDiscreteRepresentation A)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    {iota : Type*}
    (M : iota → ClosedSubgroup G)
    (hMK : ∀ i, (M i).toSubgroup ≤ K.toSubgroup)
    (hnormalM : ∀ i, (extensionSubgroup (G := G) K (M i) (hMK i)).Normal)
    (a : ∀ i,
      (extensionFixedRepresentation A K (M i) (hMK i) (hnormalM i)).V)
    (hstabilizer : ∀ i,
      representationStabilizer
        (extensionFixedRepresentation A K (M i) (hMK i) (hnormalM i)) (a i) = ⊥)
    (hintersect :
      (⨅ i, extensionSubgroup (G := G) K (M i) (hMK i)) =
        extensionSubgroup (G := G) K L hLK) :
    closedSetFixingSubgroup A hcontinuous K (Set.range fun i => (a i).1) = L := by
  ext sigma
  change sigma ∈
      closedSetFixingSubgroup A hcontinuous K (Set.range fun i => (a i).1) ↔
    sigma ∈ L
  rw [mem_closedSetFixingSubgroup_iff]
  constructor
  · rintro ⟨hsigmaK, hfix⟩
    let k : K.toSubgroup := ⟨sigma, hsigmaK⟩
    have hk_all : k ∈ ⨅ i, extensionSubgroup (G := G) K (M i) (hMK i) := by
      rw [Subgroup.mem_iInf]
      intro i
      apply (extensionFixedRepresentation_val_fixed_iff_mem
        A K (M i) (hMK i) (a i) (hstabilizer i) k).1
      exact hfix (a i).1 ⟨i, rfl⟩
    have hkL : k ∈ extensionSubgroup (G := G) K L hLK := by
      rw [← hintersect]
      exact hk_all
    exact (mem_extensionSubgroup_iff K L hLK k).1 hkL
  · intro hsigmaL
    have hsigmaK : sigma ∈ K := hLK hsigmaL
    refine ⟨hsigmaK, ?_⟩
    rintro _ ⟨i, rfl⟩
    let k : K.toSubgroup := ⟨sigma, hsigmaK⟩
    apply (extensionFixedRepresentation_val_fixed_iff_mem
      A K (M i) (hMK i) (a i) (hstabilizer i) k).2
    have hkL : k ∈ extensionSubgroup (G := G) K L hLK :=
      (mem_extensionSubgroup_iff K L hLK k).2 hsigmaL
    have hk_all : k ∈ ⨅ j, extensionSubgroup (G := G) K (M j) (hMK j) := by
      rw [hintersect]
      exact hkL
    exact (Subgroup.mem_iInf.mp hk_all) i

/-- Finite abelian endpoint of the forward direction of the finite abelian Kummer decomposition.

The finite abelian quotient is decomposed into cyclic coordinates.  The
global cyclic-operator theorem produces one radical for each coordinate;
their ambient values form a finite set `S`.  The conclusions say that
`wp(S)` is fixed by `G_K` (the abstract `Delta` inclusion) and that the
pointwise fixing subgroup of `S` is exactly `G_L` (the generation
`L = K(S)`). -/
theorem finiteAbelian_globalOperator_generators
    [IsTopologicalGroup G]
    (A : Rep ℤ G) (hAxiom : SatisfiesCyclicNormKernelVanishing A)
    (hcontinuous : IsContinuousDiscreteRepresentation A)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    [IsMulCommutative
      (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    (wp : A ⟶ A) (n : ℕ+) (xi : A.V)
    (hxi_order : addOrderOf xi = (n : ℕ))
    (hxi_kernel : wp.hom xi = 0)
    (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
    (hexponent :
      ∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK,
        q ^ (n : ℕ) = 1) :
    ∃ S : Set A.V,
      S.Finite ∧
      (∀ a, a ∈ S → ∀ k : K.toSubgroup,
        A.ρ k.1 (wp.hom a) = wp.hom a) ∧
      closedSetFixingSubgroup A hcontinuous K S = L := by
  obtain ⟨iota, hiota, m, _hm, f, hf, hfaithful⟩ :=
    open scoped IsMulCommutative in
    finiteCommGroup_exists_jointlyFaithful_cyclic_factors
      (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)
  let : Fintype iota := hiota
  let M : iota → ClosedSubgroup G := fun i =>
    closedCyclicFactorSubgroup K L hLK (f i)
  have hMK (i : iota) : (M i).toSubgroup ≤ K.toSubgroup := by
    exact closedCyclicFactorSubgroup_le_base K L hLK (f i)
  have hnormalM (i : iota) :
      (extensionSubgroup (G := G) K (M i) (hMK i)).Normal := by
    dsimp only [M]
    infer_instance
  have hfiniteM (i : iota) :
      Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i)) := by
    let : NeZero (m i) := ⟨(Nat.zero_lt_one.trans (_hm i)).ne'⟩
    exact finite_extensionSubgroup_closedCyclicFactorSubgroup_quotient
      K L hLK (f i) (hf i)
  have hcyclicM (i : iota) :
      IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i)) := by
    exact cyclic_extensionSubgroup_closedCyclicFactorSubgroup_quotient
      K L hLK (f i) (hf i)
  have hexponentM (i : iota) :
      ∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i),
        q ^ (n : ℕ) = 1 := by
    exact extensionSubgroup_closedCyclicFactorSubgroup_quotient_pow_eq_one
      K L hLK (f i) hexponent
  have hexists (i : iota) :
      ∃ a : (extensionFixedRepresentation A K (M i) (hMK i) (hnormalM i)).V,
        (∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i),
          (extensionFixedRepresentation A K (M i) (hMK i) (hnormalM i)).ρ q
              ((extensionFixedEndomorphism A K (M i) (hMK i) wp).hom a) =
            (extensionFixedEndomorphism A K (M i) (hMK i) wp).hom a) ∧
        representationStabilizer
          (extensionFixedRepresentation A K (M i) (hMK i) (hnormalM i)) a = ⊥ := by
    let : (extensionSubgroup (G := G) K (M i) (hMK i)).Normal := hnormalM i
    let : Finite
        (K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i)) :=
      hfiniteM i
    let : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i)) :=
      hcyclicM i
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α :=
      K.toSubgroup ⧸ extensionSubgroup (G := G) K (M i) (hMK i))
    exact cyclicGlobalOperator_singleRadical
      A hAxiom K (M i) (hMK i) g hg wp n xi hxi_order hxi_kernel hxi_fixed
        (hexponentM i)
  choose a hwp_fixed hstabilizer using hexists
  let S : Set A.V := Set.range fun i => (a i).1
  have hintersect :
      (⨅ i, extensionSubgroup (G := G) K (M i) (hMK i)) =
        extensionSubgroup (G := G) K L hLK := by
    change
      (⨅ i, extensionSubgroup (G := G) K
        (closedCyclicFactorSubgroup K L hLK (f i))
          (closedCyclicFactorSubgroup_le_base K L hLK (f i))) =
        extensionSubgroup (G := G) K L hLK
    simp_rw [extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK]
    exact iInf_cyclicFactorSubgroup_eq
      (extensionSubgroup (G := G) K L hLK) f hfaithful
  refine ⟨S, Set.finite_range _, ?_, ?_⟩
  · intro b hb k
    obtain ⟨i, rfl⟩ := hb
    exact extensionFixedEndomorphism_fixed_val
      A K (M i) (hMK i) wp (a i) (hwp_fixed i) k
  · exact closedSetFixingSubgroup_range_extensionFixed_eq
      A hcontinuous K L hLK M hMK hnormalM a hstabilizer hintersect

end
end KummerTheory
