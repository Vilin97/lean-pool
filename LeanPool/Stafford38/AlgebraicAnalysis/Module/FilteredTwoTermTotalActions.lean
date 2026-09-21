/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalPages

/-!
# Total direct-sum actions on filtered two-term pages

This file packages the source and target page actions of a filtered operator
into maps on the total direct sums.  The index shift is part of the map: an
operator of degree `d` sends the summand at `p` to the summand at `p - d`.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

namespace PageOperator

variable {K} {d : ℤ} (P : K.PageOperator d)

private theorem target_lof_transport (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.TargetPage r p) :
    DirectSum.lof k ℤ (fun i : ℤ => K.TargetPage r i) p x =
      DirectSum.lof k ℤ (fun i : ℤ => K.TargetPage r i) q (h ▸ x) := by
  subst q
  rfl

private theorem targetPageCast_eq_cast (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.TargetPage r p) :
    targetPageCast (K := K) r h x = h ▸ x := by
  refine Submodule.Quotient.induction_on
    ((K.boundaries r p).comap (K.G p).subtype) x ?_
  intro z
  rw [targetPageCast_mk]
  cases h
  rfl

/-- The source-page action on the total direct sum. -/
def sourceTotalMap (r : ℕ) : K.SourceTotal r →ₗ[k] K.SourceTotal r :=
  DirectSum.toModule k ℤ (K.SourceTotal r) (fun p : ℤ =>
    (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) (p - d)).comp
      (P.sourceMap r p))

/-- The target-page action on the total direct sum. -/
def targetTotalMap (r : ℕ) : K.TargetTotal r →ₗ[k] K.TargetTotal r :=
  DirectSum.toModule k ℤ (K.TargetTotal r) (fun p : ℤ =>
    (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p - d)).comp
      (P.targetMap r p))

@[simp] theorem sourceTotalMap_lof (r : ℕ) (p : ℤ) (x : K.SourcePage r p) :
    P.sourceTotalMap r
        (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p x) =
      DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) (p - d)
        (P.sourceMap r p x) := by
  rw [sourceTotalMap, DirectSum.toModule_lof]
  rfl

@[simp] theorem targetTotalMap_lof (r : ℕ) (p : ℤ) (x : K.TargetPage r p) :
    P.targetTotalMap r
        (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) p x) =
      DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p - d)
        (P.targetMap r p x) := by
  rw [targetTotalMap, DirectSum.toModule_lof]
  rfl

/-- The total action intertwines the total page differential. -/
theorem totalDrop_intertwines (r : ℕ) :
    K.totalDrop r ∘ₗ P.sourceTotalMap r =
      P.targetTotalMap r ∘ₗ K.totalDrop r := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
      rw [show DirectSum.of (fun q : ℤ => K.SourcePage r q) p y =
        DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p y from rfl]
      change K.totalDrop r (P.sourceTotalMap r
        (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p y)) =
        P.targetTotalMap r (K.totalDrop r
          (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p y))
      rw [P.sourceTotalMap_lof, K.totalDrop_lof, K.totalDrop_lof,
        P.targetTotalMap_lof]
      have h : p + (r : ℤ) - d = p - d + (r : ℤ) := by omega
      rw [target_lof_transport (K := K) r h]
      congr 1
      symm
      convert P.targetMap_drop r p y using 1
      exact (targetPageCast_eq_cast (K := K) r _ _).symm
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy


private theorem source_lof_mk_eq_of_lower (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.cycles r p) (y : K.cycles r q)
    (hxy : (x : M) - (y : M) ∈ K.G (p + 1)) :
    DirectSum.lof k ℤ (fun i => K.SourcePage r i) p (Submodule.Quotient.mk x) =
      DirectSum.lof k ℤ (fun i => K.SourcePage r i) q (Submodule.Quotient.mk y) := by
  subst q
  congr 1
  apply (Submodule.Quotient.eq _).2
  exact hxy

private theorem target_lof_mk_eq_of_lower (r : ℕ) {p q : ℤ} (h : p = q)
    (x : K.G p) (y : K.G q)
    (hxy : (x : M) - (y : M) ∈ K.G (p + 1)) :
    DirectSum.lof k ℤ (fun i => K.TargetPage r i) p (Submodule.Quotient.mk x) =
      DirectSum.lof k ℤ (fun i => K.TargetPage r i) q (Submodule.Quotient.mk y) := by
  subst q
  congr 1
  apply (Submodule.Quotient.eq _).2
  exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
    (x : M) - y, hxy, by simp⟩

/-- Lower-order commutators vanish in the total source symbol action. -/
theorem sourceTotalMap_commute_of_commutator_lowers {e : ℤ}
    (Q : K.PageOperator e)
    (hlower : ∀ p z, z ∈ K.G p →
      P.g (Q.g z) - Q.g (P.g z) ∈ K.G (p - d - e + 1)) (r : ℕ) :
    Commute (P.sourceTotalMap r) (Q.sourceTotalMap r) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p z =>
    change P.sourceTotalMap r (Q.sourceTotalMap r
      (DirectSum.lof k ℤ (fun i => K.SourcePage r i) p z)) =
      Q.sourceTotalMap r (P.sourceTotalMap r
      (DirectSum.lof k ℤ (fun i => K.SourcePage r i) p z))
    rw [Q.sourceTotalMap_lof, P.sourceTotalMap_lof,
      P.sourceTotalMap_lof, Q.sourceTotalMap_lof]
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      rw [Q.sourceMap_mk, P.sourceMap_mk, P.sourceMap_mk, Q.sourceMap_mk]
      apply source_lof_mk_eq_of_lower (K := K) r (by omega)
      change P.g (Q.g (z : M)) - Q.g (P.g (z : M)) ∈ K.G (p - e - d + 1)
      simpa only [sub_sub, add_comm] using hlower p (z : M) z.property.1
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Lower-order commutators vanish in the total target symbol action. -/
theorem targetTotalMap_commute_of_commutator_lowers {e : ℤ}
    (Q : K.PageOperator e)
    (hlower : ∀ p z, z ∈ K.G p →
      P.g (Q.g z) - Q.g (P.g z) ∈ K.G (p - d - e + 1)) (r : ℕ) :
    Commute (P.targetTotalMap r) (Q.targetTotalMap r) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p z =>
    change P.targetTotalMap r (Q.targetTotalMap r
      (DirectSum.lof k ℤ (fun i => K.TargetPage r i) p z)) =
      Q.targetTotalMap r (P.targetTotalMap r
      (DirectSum.lof k ℤ (fun i => K.TargetPage r i) p z))
    rw [Q.targetTotalMap_lof, P.targetTotalMap_lof,
      P.targetTotalMap_lof, Q.targetTotalMap_lof]
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      rw [Q.targetMap_mk, P.targetMap_mk, P.targetMap_mk, Q.targetMap_mk]
      apply target_lof_mk_eq_of_lower (K := K) r (by omega)
      change P.g (Q.g (z : M)) - Q.g (P.g (z : M)) ∈ K.G (p - e - d + 1)
      simpa only [sub_sub, add_comm] using hlower p (z : M) z.property
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy


end PageOperator

end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
