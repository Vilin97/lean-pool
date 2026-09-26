/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RealModule
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Leading
public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Algebra.Order.Ring.StandardPart

/-!
# The real Archimedean stratum of the surreal numbers

The embedded real line complements the infinitesimal surreal numbers inside the finite surreal
numbers. This module packages that familiar standard-part decomposition as a distinguished
Archimedean stratum. All other strata may still be chosen arbitrarily.

This choice makes splitting a surreal Hahn series supported on real exponents transparent: the
outer exponents remain real and every inner exponent is zero.
-/

public noncomputable section

open FiniteArchimedeanClass

namespace Surreal

/-- The standard embedding of the reals into the surreal numbers as a linear map. -/
def realLinearMap : ℝ →ₗ[ℝ] Surreal where
  toFun r := (r : Surreal)
  map_add' r s := by simp
  map_smul' r s := by
    change ((r * s : ℝ) : Surreal) = (r : Surreal) * (s : Surreal)
    exact Real.toSurrealRingHom.map_mul r s

/-- The embedded real line as a real subspace of the surreal numbers. -/
def realStratum : Submodule ℝ Surreal := LinearMap.range realLinearMap

/-- A surreal number belongs to the real stratum exactly when it is an embedded real number. -/
theorem mem_realStratum_iff {x : Surreal} :
    x ∈ realStratum ↔ ∃ r : ℝ, (r : Surreal) = x :=
  Iff.rfl

/-- The ordered additive identification of the real line with the real surreal stratum. -/
def realOrderAddMonoidIso : ℝ ≃+o realStratum :=
  { LinearEquiv.ofInjective realLinearMap (by
      intro r s h
      change (r : Surreal) = (s : Surreal) at h
      exact_mod_cast h) with
    map_le_map_iff' := by
      intro r s
      change (r : Surreal) ≤ (s : Surreal) ↔ r ≤ s
      exact Real.toSurreal_le_iff }

@[simp]
theorem coe_realOrderAddMonoidIso (r : ℝ) :
    (realOrderAddMonoidIso r : Surreal) = r :=
  (rfl)

/-- The finite Archimedean class of every nonzero real surreal number. -/
def realFiniteClass : FiniteArchimedeanClass Surreal :=
  FiniteArchimedeanClass.mk (1 : Surreal) one_ne_zero

@[simp]
theorem realFiniteClass_val : realFiniteClass.val = 0 := by
  rw [realFiniteClass]
  exact ArchimedeanClass.mk_one

/-- The infinitesimal ball and the embedded real line meet only at zero. -/
theorem disjoint_ball_realStratum :
    Disjoint (ball ℝ realFiniteClass) realStratum := by
  rw [Submodule.disjoint_def]
  intro x hxBall hxReal
  obtain ⟨r, rfl⟩ := hxReal
  by_cases hr : r = 0
  · simp [hr]
  have hrSurreal : (r : Surreal) ≠ 0 := by simp [hr]
  have hlt := (mem_ball_iff ℝ).mp hxBall hrSurreal
  exfalso
  change (realFiniteClass : ArchimedeanClass Surreal) <
    ArchimedeanClass.mk (r : Surreal) at hlt
  rw [realFiniteClass_val, Surreal.mk_realCast hr] at hlt
  exact (lt_irrefl _ hlt).elim

/-- Every finite surreal number is uniquely a real number plus an infinitesimal. -/
theorem ball_sup_realStratum_eq :
    ball ℝ realFiniteClass ⊔ realStratum = closedBall ℝ realFiniteClass := by
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨(ball_lt_closedBall (K := ℝ)).le, ?_⟩
    rintro _ ⟨r, rfl⟩
    rw [mem_closedBall_iff]
    intro hr
    apply le_of_eq
    apply Subtype.ext
    rw [realFiniteClass_val]
    change 0 = ArchimedeanClass.mk (r : Surreal)
    exact (Surreal.mk_realCast (by simpa [realLinearMap] using hr)).symm
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxmk : 0 ≤ ArchimedeanClass.mk x := by
      have h := (mem_closedBall_iff ℝ).mp hx hx0
      change (realFiniteClass : ArchimedeanClass Surreal) ≤ ArchimedeanClass.mk x at h
      simpa only [realFiniteClass_val] using h
    let r := ArchimedeanClass.stdPart x
    have hresidual : x - (r : Surreal) ∈ ball ℝ realFiniteClass := by
      rw [mem_ball_iff]
      intro _hne
      rw [← Subtype.coe_lt_coe, realFiniteClass_val]
      exact ArchimedeanClass.mk_sub_stdPart_pos Real.toSurrealRingHom hxmk
    have hreal : (r : Surreal) ∈ realStratum := ⟨r, rfl⟩
    rw [← sub_add_cancel x (r : Surreal)]
    have hresidual' : x - (r : Surreal) ∈ ball ℝ realFiniteClass ⊔ realStratum :=
      (show ball ℝ realFiniteClass ≤ ball ℝ realFiniteClass ⊔ realStratum from le_sup_left)
        hresidual
    have hreal' : (r : Surreal) ∈ ball ℝ realFiniteClass ⊔ realStratum :=
      (show realStratum ≤ ball ℝ realFiniteClass ⊔ realStratum from le_sup_right) hreal
    exact (ball ℝ realFiniteClass ⊔ realStratum).add_mem hresidual' hreal'

/-- Replace the stratum at the real Archimedean class by the embedded real line. -/
def archimedeanStrataWithReal
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal) :
    HahnEmbedding.ArchimedeanStrata ℝ Surreal where
  stratum c := if c = realFiniteClass then realStratum else u.stratum c
  disjoint_ball_stratum c := by
    classical
    by_cases hc : c = realFiniteClass
    · subst c
      simpa using disjoint_ball_realStratum
    · simp only [hc, ↓reduceIte]
      exact u.disjoint_ball_stratum c
  ball_sup_stratum_eq c := by
    classical
    by_cases hc : c = realFiniteClass
    · subst c
      simpa using ball_sup_realStratum_eq
    · simp only [hc, ↓reduceIte]
      exact u.ball_sup_stratum_eq c

@[simp]
theorem archimedeanStrataWithReal_stratum_real
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal) :
    (archimedeanStrataWithReal u).stratum realFiniteClass = realStratum := by
  simp [archimedeanStrataWithReal]

/-- The real coordinate on the distinguished stratum of `archimedeanStrataWithReal`. -/
def archimedeanStrataWithRealOrderAddMonoidIso
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal) :
    ℝ ≃+o (archimedeanStrataWithReal u).stratum realFiniteClass where
  toFun r := ⟨(r : Surreal), by
    rw [archimedeanStrataWithReal_stratum_real]
    exact ⟨r, rfl⟩⟩
  invFun x := ArchimedeanClass.stdPart (x : Surreal)
  left_inv r := ArchimedeanClass.stdPart_map_real Real.toSurrealRingHom r
  right_inv x := by
    apply Subtype.ext
    have hx : (x : Surreal) ∈ realStratum := by
      rw [← archimedeanStrataWithReal_stratum_real u]
      exact x.2
    obtain ⟨r, hr⟩ := hx
    change ((ArchimedeanClass.stdPart (x : Surreal) : ℝ) : Surreal) = x
    rw [← hr]
    change ((ArchimedeanClass.stdPart (r : Surreal) : ℝ) : Surreal) = (r : Surreal)
    exact congrArg (fun s : ℝ ↦ (s : Surreal))
      (ArchimedeanClass.stdPart_map_real Real.toSurrealRingHom r)
  map_add' r s := by
    apply Subtype.ext
    simp
  map_le_map_iff' := by
    intro r s
    change (r : Surreal) ≤ (s : Surreal) ↔ r ≤ s
    exact Real.toSurreal_le_iff

@[simp]
theorem coe_archimedeanStrataWithRealOrderAddMonoidIso
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal) (r : ℝ) :
    (archimedeanStrataWithRealOrderAddMonoidIso u r : Surreal) = r :=
  (rfl)

end Surreal
