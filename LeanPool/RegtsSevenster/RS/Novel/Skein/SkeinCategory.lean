/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomCompose
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic
public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLawRight

/-!
# The skein category: the axioms on Hom spaces

The skein category — the accompanying paper's connection category
`𝒞_f` (§3.2): identities are strand bundle classes and
composition is the descended bilinear composition.  Every axiom
reduces to a kernel membership of a difference of free-module
elements, proven by linear induction
with the per-single case supplied by a fragment equivalence
(identity laws, associativity) through isomorphism invariance.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The single difference of equivalent fragments lies in the
pairing kernel. -/
theorem mem_ker_single_sub_of_equiv {t : ℕ}
    {F G : Fragment (Fin t)} (h : F.Equiv G) :
    Finsupp.single F (1 : ℂ) - Finsupp.single G 1 ∈
      LinearMap.ker (connectionMap f.val t) := by
  rw [LinearMap.mem_ker, map_sub]
  funext K
  change connectionMap f.val t (Finsupp.single F 1) K -
    connectionMap f.val t (Finsupp.single G 1) K = 0
  rw [connectionMap_single, connectionMap_single, one_mul,
    one_mul,
    show connectionPairing f.val t F K =
        connectionPairing f.val t G K from
      f.iso_invariant _ _
        (pairCloseCongr h (Fragment.Equiv.refl K))]
  ring

/-- Equivalent fragments have equal classes. -/
theorem HomSpace.ofFragment_congr {t : ℕ}
    {F G : Fragment (Fin t)} (h : F.Equiv G) :
    HomSpace.ofFragment f.val F =
      HomSpace.ofFragment f.val G :=
  (Submodule.Quotient.eq _).mpr
    (mem_ker_single_sub_of_equiv f h)

/-- The single difference of a weighted pair of equivalent
fragments lies in the kernel. -/
theorem mem_ker_single_sub_of_equiv_smul {t : ℕ}
    {F G : Fragment (Fin t)} (h : F.Equiv G) (c : ℂ) :
    Finsupp.single F c - Finsupp.single G c ∈
      LinearMap.ker (connectionMap f.val t) := by
  have h1 : Finsupp.single F c - Finsupp.single G c =
      c • (Finsupp.single F (1 : ℂ) - Finsupp.single G 1) := by
    rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  rw [h1]
  exact Submodule.smul_mem _ c
    (mem_ker_single_sub_of_equiv f h)

/-- The left unit difference lies in the kernel. -/
theorem mem_ker_id_left (s u : ℕ)
    (y : Fragment (Fin (s + u)) →₀ ℂ) :
    composeFinsupp s s u
        (Finsupp.single (strandBundle s) 1) y - y ∈
      LinearMap.ker (connectionMap f.val (s + u)) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, sub_zero]
    exact Submodule.zero_mem _
  | add y z hy hz =>
    have h1 : composeFinsupp s s u
        (Finsupp.single (strandBundle s) 1) (y + z) - (y + z) =
        (composeFinsupp s s u
          (Finsupp.single (strandBundle s) 1) y - y) +
        (composeFinsupp s s u
          (Finsupp.single (strandBundle s) 1) z - z) := by
      rw [map_add]
      abel
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | single F c =>
    rw [composeFinsupp_single, one_mul]
    exact mem_ker_single_sub_of_equiv_smul f
      (composeStrandBundleLeft s u F) c

/-- The right unit difference lies in the kernel. -/
theorem mem_ker_id_right (s u : ℕ)
    (y : Fragment (Fin (s + u)) →₀ ℂ) :
    composeFinsupp s u u y
        (Finsupp.single (strandBundle u) 1) - y ∈
      LinearMap.ker (connectionMap f.val (s + u)) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add y z hy hz =>
    have h1 : composeFinsupp s u u (y + z)
        (Finsupp.single (strandBundle u) 1) - (y + z) =
        (composeFinsupp s u u y
          (Finsupp.single (strandBundle u) 1) - y) +
        (composeFinsupp s u u z
          (Finsupp.single (strandBundle u) 1) - z) := by
      rw [map_add, LinearMap.add_apply]
      abel
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | single F c =>
    rw [composeFinsupp_single, mul_one]
    exact mem_ker_single_sub_of_equiv_smul f
      (composeStrandBundleRight s u F) c

/-- The associativity difference lies in the kernel. -/
theorem mem_ker_assoc (s t u v : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ)
    (y : Fragment (Fin (t + u)) →₀ ℂ)
    (z : Fragment (Fin (u + v)) →₀ ℂ) :
    composeFinsupp s u v (composeFinsupp s t u x y) z -
        composeFinsupp s t v x (composeFinsupp t u v y z) ∈
      LinearMap.ker (connectionMap f.val (s + v)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]
    exact Submodule.zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    have he : composeFinsupp s u v
        (composeFinsupp s t u (x₁ + x₂) y) z -
        composeFinsupp s t v (x₁ + x₂)
          (composeFinsupp t u v y z) =
        (composeFinsupp s u v (composeFinsupp s t u x₁ y) z -
          composeFinsupp s t v x₁ (composeFinsupp t u v y z)) +
        (composeFinsupp s u v (composeFinsupp s t u x₂ y) z -
          composeFinsupp s t v x₂
            (composeFinsupp t u v y z)) := by
      rw [map_add, LinearMap.add_apply, map_add,
        LinearMap.add_apply, map_add, LinearMap.add_apply]
      abel
    rw [he]
    exact Submodule.add_mem _ h₁ h₂
  | single F c =>
    induction y using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply, sub_zero]
      exact Submodule.zero_mem _
    | add y₁ y₂ h₁ h₂ =>
      have he : composeFinsupp s u v
          (composeFinsupp s t u (Finsupp.single F c)
            (y₁ + y₂)) z -
          composeFinsupp s t v (Finsupp.single F c)
            (composeFinsupp t u v (y₁ + y₂) z) =
          (composeFinsupp s u v
            (composeFinsupp s t u (Finsupp.single F c) y₁) z -
            composeFinsupp s t v (Finsupp.single F c)
              (composeFinsupp t u v y₁ z)) +
          (composeFinsupp s u v
            (composeFinsupp s t u (Finsupp.single F c) y₂) z -
            composeFinsupp s t v (Finsupp.single F c)
              (composeFinsupp t u v y₂ z)) := by
        rw [map_add, map_add, LinearMap.add_apply, map_add,
          LinearMap.add_apply, map_add]
        abel
      rw [he]
      exact Submodule.add_mem _ h₁ h₂
    | single G c' =>
      induction z using Finsupp.induction_linear with
      | zero =>
        rw [map_zero, map_zero, map_zero, sub_zero]
        exact Submodule.zero_mem _
      | add z₁ z₂ h₁ h₂ =>
        have he : composeFinsupp s u v
            (composeFinsupp s t u (Finsupp.single F c)
              (Finsupp.single G c')) (z₁ + z₂) -
            composeFinsupp s t v (Finsupp.single F c)
              (composeFinsupp t u v (Finsupp.single G c')
                (z₁ + z₂)) =
            (composeFinsupp s u v
              (composeFinsupp s t u (Finsupp.single F c)
                (Finsupp.single G c')) z₁ -
              composeFinsupp s t v (Finsupp.single F c)
                (composeFinsupp t u v (Finsupp.single G c')
                  z₁)) +
            (composeFinsupp s u v
              (composeFinsupp s t u (Finsupp.single F c)
                (Finsupp.single G c')) z₂ -
              composeFinsupp s t v (Finsupp.single F c)
                (composeFinsupp t u v (Finsupp.single G c')
                  z₂)) := by
          rw [map_add, map_add, map_add]
          abel
        rw [he]
        exact Submodule.add_mem _ h₁ h₂
      | single H c'' =>
        rw [composeFinsupp_single, composeFinsupp_single,
          composeFinsupp_single, composeFinsupp_single]
        rw [show c * c' * c'' = c * (c' * c'') by ring]
        exact mem_ker_single_sub_of_equiv_smul f
          (composeAssoc F G H) (c * (c' * c''))

/-! ### The axioms on quotient classes -/

/-- Left unit law on classes. -/
theorem HomSpace.comp_id_left (s u : ℕ)
    (q : HomSpace f.val (s + u)) :
    HomSpace.comp f s s u
      (HomSpace.ofFragment f.val (strandBundle s)) q = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (Submodule.Quotient.eq _).mpr (mem_ker_id_left f s u y)

/-- Right unit law on classes. -/
theorem HomSpace.comp_id_right (s u : ℕ)
    (q : HomSpace f.val (s + u)) :
    HomSpace.comp f s u u q
      (HomSpace.ofFragment f.val (strandBundle u)) = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (Submodule.Quotient.eq _).mpr (mem_ker_id_right f s u y)

/-- Associativity on classes. -/
theorem HomSpace.comp_assoc (s t u v : ℕ)
    (p : HomSpace f.val (s + t)) (q : HomSpace f.val (t + u))
    (r : HomSpace f.val (u + v)) :
    HomSpace.comp f s u v (HomSpace.comp f s t u p q) r =
      HomSpace.comp f s t v p (HomSpace.comp f t u v q r) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ r
  exact (Submodule.Quotient.eq _).mpr
    (mem_ker_assoc f s t u v x y z)

end RS
