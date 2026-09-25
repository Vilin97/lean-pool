/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPole
import LeanPool.BrillNoetherGraphs.Utilities.Segments.SeamCalculus

/-!
# Response profiles for a two-pole join

For a divisor on a two-pole graph, a boundary response records two fluxes and
the displacement of a winning firing script between the poles.  Two factor
responses glue exactly when their displacement difference equals the flux
difference.  This is the lossless scalar compatibility condition behind a
two-edge cut, stated directly for the reusable `TwoPole.join` constructor.

The fluxes are not restricted to canonical divisors or to genus two.  This is
intentional: marked residuals such as `4a - 2u`, higher-rank tests, and future
multi-stage gluings can all use the same interface.
-/

open Finset

namespace Utilities
namespace TwoPole

universe u v

/-- Debit the two boundary fluxes from a divisor on the left factor. -/
def debit {G : CFGraph.{u}} (p : TwoPole G) (D : CFDiv G)
    (c₁ c₂ : ℤ) : CFDiv G :=
  D - c₁ • oneChip p.first - c₂ • oneChip p.second

/-- Credit the two boundary fluxes to a divisor on the right factor. -/
def credit {G : CFGraph.{u}} (p : TwoPole G) (D : CFDiv G)
    (c₁ c₂ : ℤ) : CFDiv G :=
  D + c₁ • oneChip p.first + c₂ • oneChip p.second

/-- A response of a two-pole divisor to prescribed boundary fluxes.  The
integer `t` is the displacement of a script making the debited divisor
effective. -/
def IsDebitResponse {G : CFGraph.{u}} (p : TwoPole G) (D : CFDiv G)
    (c₁ c₂ t : ℤ) : Prop :=
  IsDisplacement (debit p D c₁ c₂) p.first p.second 0 t

/-- The credited mirror of `IsDebitResponse`. -/
def IsCreditResponse {G : CFGraph.{u}} (p : TwoPole G) (D : CFDiv G)
    (c₁ c₂ t : ℤ) : Prop :=
  IsDisplacement (credit p D c₁ c₂) p.first p.second 0 t

@[simp] theorem deg_debit {G : CFGraph.{u}} (p : TwoPole G)
    (D : CFDiv G) (c₁ c₂ : ℤ) :
    deg (debit p D c₁ c₂) = deg D - c₁ - c₂ := by
  simp only [debit, deg.map_sub, map_zsmul, deg_one_chip, smul_eq_mul]
  ring

@[simp] theorem deg_credit {G : CFGraph.{u}} (p : TwoPole G)
    (D : CFDiv G) (c₁ c₂ : ℤ) :
    deg (credit p D c₁ c₂) = deg D + c₁ + c₂ := by
  simp only [credit, deg.map_add, map_zsmul, deg_one_chip, smul_eq_mul]
  ring

/-- Glue factor scripts, translating the right script by a constant.  The
translation changes neither its factor principal divisor nor its
displacement, but it sets the absolute flux through the first cross-edge. -/
def glueScript (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) :
    firingScript (join A B p q) :=
  Sum.elim f (fun b => g b + k)

@[simp] theorem glueScript_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (a : A.V) :
    glueScript A B p q f g k (Sum.inl a) = f a := rfl

@[simp] theorem glueScript_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (b : B.V) :
    glueScript A B p q f g k (Sum.inr b) = g b + k := rfl
/-- The first bridge contributes its flux at a left vertex. -/
theorem prin_bridge_glueScript_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (a : A.V) :
    prin (bridge A B p q) (glueScript A B p q f g k) (Sum.inl a) =
      prin A f a +
        if a = p.first then g q.first + k - f p.first else 0 := by
  change
    (∑ z : Sum A.V B.V,
      (Sum.elim f (fun b => g b + k) z - f a) *
        (numEdges (bridgeGraph A B p.first q.first) (Sum.inl a) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  simp_rw [num_edges_bridgeGraph_inl, num_edges_bridgeGraph_inl_inr]
  change
    (∑ x : A.V, (f x - f a) * (numEdges A a x : ℤ)) +
      ∑ y : B.V, (g y + k - f a) *
        (((if a = p.first ∧ y = q.first then 1 else 0) : ℕ) : ℤ) = _
  by_cases ha : a = p.first
  · subst a
    simp [prin_apply]
  · simp [ha, prin_apply]
/-- The first bridge contributes its flux at a right vertex. -/
theorem prin_bridge_glueScript_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (b : B.V) :
    prin (bridge A B p q) (glueScript A B p q f g k) (Sum.inr b) =
      prin B g b +
        if b = q.first then f p.first - (g q.first + k) else 0 := by
  change
    (∑ z : Sum A.V B.V,
      (Sum.elim f (fun y => g y + k) z - (g b + k)) *
        (numEdges (bridgeGraph A B p.first q.first) (Sum.inr b) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  have hCross (a : A.V) :
      numEdges (bridgeGraph A B p.first q.first) (Sum.inr b) (Sum.inl a) =
        if a = p.first ∧ b = q.first then 1 else 0 := by
    rw [num_edges_symmetric]
    exact num_edges_bridgeGraph_inl_inr A B p.first q.first a b
  simp_rw [hCross, num_edges_bridgeGraph_inr]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hCancel (y : B.V) : g y + k - (g b + k) = g y - g b := by
    ring
  simp_rw [hCancel]
  change
    (∑ x : A.V, (f x - (g b + k)) *
        (((if x = p.first ∧ b = q.first then 1 else 0) : ℕ) : ℤ)) +
      ∑ y : B.V, (g y - g b) * (numEdges B b y : ℤ) = _
  by_cases hb : b = q.first
  · subst b
    simp [prin_apply]
    ring
  · simp [hb, prin_apply]
/-- Both cross-edges contribute their fluxes at a left vertex. -/
theorem prin_join_glueScript_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (a : A.V) :
    prin (join A B p q) (glueScript A B p q f g k) (Sum.inl a) =
      prin A f a +
        (if a = p.first then g q.first + k - f p.first else 0) +
        (if a = p.second then g q.second + k - f p.second else 0) := by
  let σ := glueScript A B p q f g k
  have hAdd := congrFun
    (prin_addEdge (bridge A B p q) (Sum.inl p.second) (Sum.inr q.second)
      (second_endpoints_ne A B p q) σ) (Sum.inl a)
  change
    prin (bridge A B p q) σ (Sum.inl a) =
      prin (join A B p q) σ (Sum.inl a) +
        (σ (Sum.inl p.second) - σ (Sum.inr q.second)) *
          seamDivisor (H := bridge A B p q)
            (Sum.inl p.second) (Sum.inr q.second) (Sum.inl a) at hAdd
  rw [prin_bridge_glueScript_inl] at hAdd
  simp only [σ, glueScript_inl, glueScript_inr] at hAdd
  change _ = _
  by_cases ha : a = p.second
  · subst a
    simp [seamDivisor, oneChip] at hAdd ⊢
    linarith
  · have hSum : (Sum.inl a : Sum A.V B.V) ≠ Sum.inl p.second :=
      fun h => ha (Sum.inl.inj h)
    simp [seamDivisor, oneChip, ha, hSum] at hAdd ⊢
    linarith
/-- Both cross-edges contribute their fluxes at a right vertex. -/
theorem prin_join_glueScript_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (f : firingScript A) (g : firingScript B) (k : ℤ) (b : B.V) :
    prin (join A B p q) (glueScript A B p q f g k) (Sum.inr b) =
      prin B g b +
        (if b = q.first then f p.first - (g q.first + k) else 0) +
        (if b = q.second then f p.second - (g q.second + k) else 0) := by
  let σ := glueScript A B p q f g k
  have hAdd := congrFun
    (prin_addEdge (bridge A B p q) (Sum.inl p.second) (Sum.inr q.second)
      (second_endpoints_ne A B p q) σ) (Sum.inr b)
  change
    prin (bridge A B p q) σ (Sum.inr b) =
      prin (join A B p q) σ (Sum.inr b) +
        (σ (Sum.inl p.second) - σ (Sum.inr q.second)) *
          seamDivisor (H := bridge A B p q)
            (Sum.inl p.second) (Sum.inr q.second) (Sum.inr b) at hAdd
  rw [prin_bridge_glueScript_inr] at hAdd
  simp only [σ, glueScript_inl, glueScript_inr] at hAdd
  change _ = _
  by_cases hb : b = q.second
  · subst b
    simp [seamDivisor, oneChip] at hAdd ⊢
    linarith
  · have hSum : (Sum.inr b : Sum A.V B.V) ≠ Sum.inr q.second :=
      fun h => hb (Sum.inr.inj h)
    simp [seamDivisor, oneChip, hb, hSum] at hAdd ⊢
    linarith
/-- **Two-pole response gluing.**  A debited response on the left and the
matching credited response on the right make the original factor sum
winnable.  The sole compatibility equation is
`left displacement - right displacement = first flux - second flux`. -/
theorem winnable_sumDivisor_of_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (c₁ c₂ s t : ℤ)
    (hLeft : IsDebitResponse p D c₁ c₂ s)
    (hRight : IsCreditResponse q E c₁ c₂ t)
    (hMatch : s - t = c₁ - c₂) :
    winnable (join A B p q) (sumDivisor A B p q D E) := by
  obtain ⟨f, hfEffective, hfDisplacement⟩ := hLeft
  obtain ⟨g, hgEffective, hgDisplacement⟩ := hRight
  have hfEffective' : effective (debit p D c₁ c₂ + prin A f) := by
    simpa [seamTwist] using hfEffective
  have hgEffective' : effective (credit q E c₁ c₂ + prin B g) := by
    simpa [seamTwist] using hgEffective
  let k : ℤ := f p.first - g q.first - c₁
  let σ := glueScript A B p q f g k
  have hFlux₁ : f p.first - (g q.first + k) = c₁ := by
    dsimp [k]
    ring
  have hFlux₂ : f p.second - (g q.second + k) = c₂ := by
    dsimp [k]
    unfold displacement at hfDisplacement hgDisplacement
    omega
  have hFlux₁' : g q.first + k - f p.first = -c₁ := by omega
  have hFlux₂' : g q.second + k - f p.second = -c₂ := by omega
  have hEffective : effective
      (sumDivisor A B p q D E + prin (join A B p q) σ) := by
    change effective
      (sumDivisor A B p q D E +
        prin (join A B p q) (glueScript A B p q f g k))
    intro z
    cases z with
    | inl a =>
        have hLocal := hfEffective' a
        have hEq :
            D a + prin (join A B p q)
                (glueScript A B p q f g k) (Sum.inl a) =
              (debit p D c₁ c₂ + prin A f) a := by
          rw [prin_join_glueScript_inl, hFlux₁', hFlux₂']
          by_cases ha₁ : a = p.first <;> by_cases ha₂ : a = p.second
          all_goals simp_all [debit, oneChip]
          all_goals ring
        change 0 ≤ D a +
          prin (join A B p q) (glueScript A B p q f g k) (Sum.inl a)
        rw [hEq]
        exact hLocal
    | inr b =>
        have hLocal := hgEffective' b
        have hEq :
            E b + prin (join A B p q)
                (glueScript A B p q f g k) (Sum.inr b) =
              (credit q E c₁ c₂ + prin B g) b := by
          rw [prin_join_glueScript_inr, hFlux₁, hFlux₂]
          by_cases hb₁ : b = q.first <;> by_cases hb₂ : b = q.second
          all_goals simp_all [credit, oneChip]
          all_goals ring
        change 0 ≤ E b +
          prin (join A B p q) (glueScript A B p q f g k) (Sum.inr b)
        rw [hEq]
        exact hLocal
  exact (winnable_add_prin_iff (sumDivisor A B p q D E) σ).mp
    (winnable_of_effective (join A B p q) _ hEffective)
/-- **Completeness of two-pole responses.**  Every global winning script
determines its two boundary fluxes and restricts to a response on each factor.
Thus the scalar compatibility equation in
`winnable_sumDivisor_of_responses` loses no information. -/
theorem exists_responses_of_winnable_sumDivisor
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B)
    (hWin : winnable (join A B p q) (sumDivisor A B p q D E)) :
    ∃ c₁ c₂ s t : ℤ,
      IsDebitResponse p D c₁ c₂ s ∧
      IsCreditResponse q E c₁ c₂ t ∧
      s - t = c₁ - c₂ := by
  obtain ⟨F, hFEffective, hEquiv⟩ :=
    (winnable_iff_exists_effective (join A B p q)
      (sumDivisor A B p q D E)).mp hWin
  obtain ⟨σ, hσ⟩ :=
    (principal_iff_eq_prin (join A B p q)
      (F - sumDivisor A B p q D E)).mp hEquiv
  have hEffective : effective
      (sumDivisor A B p q D E + prin (join A B p q) σ) := by
    have hEq : sumDivisor A B p q D E + prin (join A B p q) σ = F := by
      rw [← hσ]
      abel
    rw [hEq]
    exact hFEffective
  let f : firingScript A := fun a => σ (Sum.inl a)
  let g : firingScript B := fun b => σ (Sum.inr b)
  let c₁ : ℤ := f p.first - g q.first
  let c₂ : ℤ := f p.second - g q.second
  let s : ℤ := displacement p.first p.second f
  let t : ℤ := displacement q.first q.second g
  have hGlue : glueScript A B p q f g 0 = σ := by
    funext z
    cases z with
    | inl a => rfl
    | inr b => simp [glueScript, g]
  have hLeftEffective : effective (debit p D c₁ c₂ + prin A f) := by
    intro a
    have hGlobal := hEffective (Sum.inl a)
    change 0 ≤ D a + prin (join A B p q) σ (Sum.inl a) at hGlobal
    have hEq :
        (debit p D c₁ c₂ + prin A f) a =
          D a + prin (join A B p q) σ (Sum.inl a) := by
      rw [← hGlue, prin_join_glueScript_inl]
      dsimp [c₁, c₂]
      by_cases ha₁ : a = p.first <;> by_cases ha₂ : a = p.second
      all_goals simp_all [debit, oneChip]
      all_goals ring
    rw [hEq]
    exact hGlobal
  have hRightEffective : effective (credit q E c₁ c₂ + prin B g) := by
    intro b
    have hGlobal := hEffective (Sum.inr b)
    change 0 ≤ E b + prin (join A B p q) σ (Sum.inr b) at hGlobal
    have hEq :
        (credit q E c₁ c₂ + prin B g) b =
          E b + prin (join A B p q) σ (Sum.inr b) := by
      rw [← hGlue, prin_join_glueScript_inr]
      dsimp [c₁, c₂]
      by_cases hb₁ : b = q.first <;> by_cases hb₂ : b = q.second
      all_goals simp_all [credit, oneChip]
      all_goals ring
    rw [hEq]
    exact hGlobal
  refine ⟨c₁, c₂, s, t, ?_, ?_, ?_⟩
  · exact ⟨f, by simpa [seamTwist] using hLeftEffective, rfl⟩
  · exact ⟨g, by simpa [seamTwist] using hRightEffective, rfl⟩
  · dsimp [s, t, c₁, c₂]
    unfold displacement
    ring

/-- **Exact two-pole gluing criterion.**  A factor sum is winnable precisely
when the factors admit responses whose displacement difference equals their
flux difference. -/
theorem winnable_sumDivisor_iff_exists_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) :
    winnable (join A B p q) (sumDivisor A B p q D E) ↔
      ∃ c₁ c₂ s t : ℤ,
        IsDebitResponse p D c₁ c₂ s ∧
        IsCreditResponse q E c₁ c₂ t ∧
        s - t = c₁ - c₂ := by
  constructor
  · exact exists_responses_of_winnable_sumDivisor A B p q D E
  · rintro ⟨c₁, c₂, s, t, hLeft, hRight, hMatch⟩
    exact winnable_sumDivisor_of_responses
      A B p q D E c₁ c₂ s t hLeft hRight hMatch

end TwoPole
end Utilities
