/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.EPrimitive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupAlgebra
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupGCD
import LeanPool.ConwayRefinement.ConwayRefinement.RingTheory.LaurentTower
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Greatest common divisors of finite-support nonpositive series

LM24, Fact 2.5.2, following Gilmer and Parker, Theorem 6.4 specialized to a totally ordered
exponent group.

Two series involve only finitely many exponents, so they live in a finitely generated subgroup,
which is free of finite rank because a linearly ordered group is torsion free. Its group ring is
reached from the coefficient field by a tower of Laurent extensions and so has unique
factorisation, hence least common multiples. Those transfer to the whole exponent group one coset
at a time, and greatest common divisors on the nonpositive exponents follow by splitting at the
largest exponent.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- A finitely generated subgroup of a linearly ordered group is free of finite rank. -/
theorem exists_addEquiv_fin (S : Finset G) :
    ∃ k : ℕ, Nonempty ((AddSubgroup.closure (S : Set G)) ≃+ (Fin k → ℤ)) := by
  have heq : (AddSubgroup.closure (S : Set G)).toIntSubmodule = Submodule.span ℤ (S : Set G) :=
    AddSubgroup.toIntSubmodule_closure _
  have : Module.Finite ℤ (AddSubgroup.closure (S : Set G)) :=
    Module.Finite.iff_fg (N := (AddSubgroup.closure (S : Set G)).toIntSubmodule).mpr
      (heq ▸ Submodule.fg_span S.finite_toSet)
  obtain ⟨k, b⟩ :=
    Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := (AddSubgroup.closure (S : Set G)))
  exact ⟨k, ⟨b.equivFun.toAddEquiv⟩⟩

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- The group ring of a free subgroup of finite rank has unique factorisation. -/
theorem uniqueFactorizationMonoid_subgroupAlgebra {H : AddSubgroup G}
    (h : ∃ k : ℕ, Nonempty (H ≃+ (Fin k → ℤ))) :
    UniqueFactorizationMonoid (AddMonoidAlgebra K H) := by
  obtain ⟨k, ⟨e⟩⟩ := h
  exact MulEquiv.uniqueFactorizationMonoid
    (AddMonoidAlgebra.domCongr (R := K) (A := K) (e := e)).symm.toRingEquiv.toMulEquiv
    (AddMonoidAlgebra.uniqueFactorizationMonoid_finInt K k)

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Least common multiples in the group ring of such a subgroup. -/
theorem exists_lcm_subgroupAlgebra {H : AddSubgroup G}
    (hufm : UniqueFactorizationMonoid (AddMonoidAlgebra K H)) (a b : AddMonoidAlgebra K H) :
    ∃ c : AddMonoidAlgebra K H, ∀ d, a ∣ d ∧ b ∣ d ↔ c ∣ d := by
  have := hufm
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid (AddMonoidAlgebra K H)) := inferInstance
  let := inst
  exact ⟨lcm a b, fun d ↦ ⟨fun h ↦ lcm_dvd h.1 h.2,
    fun h ↦ ⟨(dvd_lcm_left a b).trans h, (dvd_lcm_right a b).trans h⟩⟩⟩

/-- Least common multiples of finite-support series, in the whole exponent group. -/
theorem exists_lcm_dvdFS (f g : K⟦G⟧) (hf : f.support.Finite) (hg : g.support.Finite) :
    ∃ h : K⟦G⟧, h.support.Finite ∧ ∀ m : K⟦G⟧, m.support.Finite →
      (DvdFS f m ∧ DvdFS g m ↔ DvdFS h m) := by
  classical
  -- the exponents of both arguments generate a finitely generated subgroup
  set S : Finset G := hf.toFinset ∪ hg.toFinset with hS
  set H : AddSubgroup G := AddSubgroup.closure (S : Set G) with hH
  have hfsub : f.support ⊆ (H : Set G) := fun x hx ↦
    AddSubgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_union_left _ (hf.mem_toFinset.mpr hx)))
  have hgsub : g.support ⊆ (H : Set G) := fun x hx ↦
    AddSubgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_union_right _ (hg.mem_toFinset.mpr hx)))
  have hufm : UniqueFactorizationMonoid (AddMonoidAlgebra K H) :=
    uniqueFactorizationMonoid_subgroupAlgebra (exists_addEquiv_fin S)
  obtain ⟨a, ha⟩ := exists_subgroupAlgebraHom_eq H hf hfsub
  obtain ⟨b, hb⟩ := exists_subgroupAlgebraHom_eq H hg hgsub
  obtain ⟨c, hc⟩ := exists_lcm_subgroupAlgebra hufm a b
  refine ⟨subgroupAlgebraHom H c, support_subgroupAlgebraHom_finite H c, fun m hm ↦ ?_⟩
  -- inside the subgroup the statement is the group-ring one
  have hin : ∀ n : K⟦G⟧, n.support.Finite → n.support ⊆ (H : Set G) →
      (DvdFS f n ∧ DvdFS g n → DvdFS (subgroupAlgebraHom H c) n) := by
    intro n hnf hnsub hdvd
    obtain ⟨d, hd⟩ := exists_subgroupAlgebraHom_eq H hnf hnsub
    subst hd
    rw [← ha, ← hb] at hdvd
    rw [← dvd_iff_dvdFS_subgroupAlgebraHom, ← dvd_iff_dvdFS_subgroupAlgebraHom] at hdvd
    exact (dvd_iff_dvdFS_subgroupAlgebraHom H c d).mp ((hc d).mp hdvd)
  constructor
  · rintro ⟨h1, h2⟩
    refine dvdFS_of_forall_subgroup hfsub hgsub ?_ hm h1 h2
    intro n hnf hnsub hn1 hn2
    exact hin n hnf hnsub ⟨hn1, hn2⟩
  · intro hdvd
    have hcf : DvdFS f (subgroupAlgebraHom H c) := by
      rw [← ha, ← dvd_iff_dvdFS_subgroupAlgebraHom]
      exact ((hc c).mpr dvd_rfl).1
    have hcg : DvdFS g (subgroupAlgebraHom H c) := by
      rw [← hb, ← dvd_iff_dvdFS_subgroupAlgebraHom]
      exact ((hc c).mpr dvd_rfl).2
    exact ⟨hcf.trans hdvd, hcg.trans hdvd⟩

/-- Divisibility in the finite-support ring is divisibility with a finite-support quotient. -/
theorem dvd_iff_dvdFS (a b : (HahnSeries.finiteSupportSubring : Subring K⟦G⟧)) :
    a ∣ b ↔ DvdFS (a : K⟦G⟧) (b : K⟦G⟧) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact dvdFS_iff.mpr
      ⟨(c : K⟦G⟧), (HahnSeries.mem_finiteSupportSubring_iff _).mp c.2, rfl⟩
  · intro h
    obtain ⟨w, hwf, hw⟩ := dvdFS_iff.mp h
    exact ⟨⟨w, (HahnSeries.mem_finiteSupportSubring_iff w).mpr hwf⟩, Subtype.ext hw⟩

open Classical in
/-- Greatest common divisors of finite-support series, in the whole exponent group. -/
theorem exists_gcd_dvdFS (x z : K⟦G⟧) (hx : x.support.Finite) (hz : z.support.Finite) :
    ∃ d : K⟦G⟧, d.support.Finite ∧
      ∀ e : K⟦G⟧, e.support.Finite → (DvdFS e x ∧ DvdFS e z ↔ DvdFS e d) := by
  let : GCDMonoid (HahnSeries.finiteSupportSubring : Subring K⟦G⟧) := by
    refine gcdMonoidOfExistsLCM fun a b ↦ ?_
    obtain ⟨h, hhf, hh⟩ := exists_lcm_dvdFS (a : K⟦G⟧) (b : K⟦G⟧)
      ((HahnSeries.mem_finiteSupportSubring_iff _).mp a.2)
      ((HahnSeries.mem_finiteSupportSubring_iff _).mp b.2)
    refine ⟨⟨h, (HahnSeries.mem_finiteSupportSubring_iff h).mpr hhf⟩, fun d ↦ ?_⟩
    rw [dvd_iff_dvdFS, dvd_iff_dvdFS, dvd_iff_dvdFS]
    exact hh (d : K⟦G⟧) ((HahnSeries.mem_finiteSupportSubring_iff _).mp d.2)
  set a : (HahnSeries.finiteSupportSubring : Subring K⟦G⟧) :=
    ⟨x, (HahnSeries.mem_finiteSupportSubring_iff x).mpr hx⟩ with ha
  set b : (HahnSeries.finiteSupportSubring : Subring K⟦G⟧) :=
    ⟨z, (HahnSeries.mem_finiteSupportSubring_iff z).mpr hz⟩ with hb
  set d : (HahnSeries.finiteSupportSubring : Subring K⟦G⟧) := gcd a b with hd
  refine ⟨(d : K⟦G⟧), (HahnSeries.mem_finiteSupportSubring_iff _).mp d.2, fun e hef ↦ ?_⟩
  set c : (HahnSeries.finiteSupportSubring : Subring K⟦G⟧) :=
    ⟨e, (HahnSeries.mem_finiteSupportSubring_iff e).mpr hef⟩ with hc
  rw [show x = (a : K⟦G⟧) from rfl, show z = (b : K⟦G⟧) from rfl,
    show e = (c : K⟦G⟧) from rfl, ← dvd_iff_dvdFS, ← dvd_iff_dvdFS, ← dvd_iff_dvdFS, hd]
  exact ⟨fun hq ↦ dvd_gcd hq.1 hq.2,
    fun hq ↦ ⟨hq.trans (gcd_dvd_left a b), hq.trans (gcd_dvd_right a b)⟩⟩

namespace Nonpositive

/-- Divisibility in the nonpositive finite-support ring. -/
theorem dvd_iff_dvdNP (a b : (finiteSupportSubring : Subring (Nonpositive G K))) :
    a ∣ b ↔ DvdNP ((a : Nonpositive G K) : K⟦G⟧) ((b : Nonpositive G K) : K⟦G⟧) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact dvdNP_iff.mpr ⟨((c : Nonpositive G K) : K⟦G⟧),
      (mem_finiteSupportSubring_iff _).mp c.2,
      (HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (c : Nonpositive G K).2, rfl⟩
  · intro h
    obtain ⟨w, hwf, hws, hw⟩ := dvdNP_iff.mp h
    refine ⟨⟨⟨w, (HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mpr hws⟩,
      (mem_finiteSupportSubring_iff _).mpr hwf⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hw)

/-- LM24, Fact 2.5.2: every pair of finite-support nonpositive series has a greatest common
divisor. -/
@[blueprint "fact:finite-support-hahn-gcd"
  (phase := "Primality and factorisation for real exponents")
  (title := "Greatest common divisors of finite-support series")
  (statement := /--
    Let $G$ be a linearly ordered abelian group and $K$ a field.  For all $p,q$
    in the finite-support subring $K(G^{\le 0})$ of $K((G^{\le 0}))$, there is
    $d\in K(G^{\le 0})$ such that, for every $e\in K(G^{\le 0})$,
    \[
      e\mid p\ \text{and}\ e\mid q \quad\Longleftrightarrow\quad e\mid d.
    \]
    This is the greatest-common-divisor assertion of [LM24, Fact 2.5.2].
  -/)
  (proof := /--
    The zero cases are immediate.  Otherwise, the supports of $p$ and $q$
    generate a finite-rank free subgroup $H$ of $G$.  Finite-support series with
    exponents in $H$ form a Laurent polynomial ring, hence a unique factorisation
    domain.  Compute a least common multiple there, compare coefficients on
    cosets of $H$ to transfer divisibility to finite-support series with exponents
    in $G$, and use the lcm-to-gcd construction.  Write each input as a monomial
    times a series whose support meets $0$, and translate the resulting gcd by
    the larger of the two monomial exponents.  The gcd and its two cofactors then
    have nonpositive support.
  -/)]
theorem finiteSupport_pairwise_gcd_exists
    (p q : (finiteSupportSubring : Subring (Nonpositive G K))) :
    ∃ d : (finiteSupportSubring : Subring (Nonpositive G K)),
      ∀ e : (finiteSupportSubring : Subring (Nonpositive G K)),
        e ∣ p ∧ e ∣ q ↔ e ∣ d := by
  obtain ⟨d, hdf, hds, hd⟩ := exists_gcd_nonpositive_of_exists_gcd
    (fun x z hx hz ↦ exists_gcd_dvdFS x z hx hz)
    ((mem_finiteSupportSubring_iff _).mp p.2)
    ((HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (p : Nonpositive G K).2)
    ((mem_finiteSupportSubring_iff _).mp q.2)
    ((HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (q : Nonpositive G K).2)
  refine ⟨⟨⟨d, (HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mpr hds⟩,
    (mem_finiteSupportSubring_iff _).mpr hdf⟩, fun e ↦ ?_⟩
  rw [dvd_iff_dvdNP, dvd_iff_dvdNP, dvd_iff_dvdNP]
  exact hd _ ((mem_finiteSupportSubring_iff _).mp e.2)
    ((HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (e : Nonpositive G K).2)

end Nonpositive

end HahnSeries
