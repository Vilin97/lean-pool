/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStar

/-!
# The five-observer path (A4)

Statements split from the original `Statements.lean` skeleton (one file per proving task).
Everything in this file is proved; the order-`t` witness `fivePath_witness` and its expressible form live in `InflationGraphOpen/FivePath.lean`. See AUDIT-NOTES A4 for the mathematics.

`FivePathAux` collects the auxiliary material: the explicit enumeration of the 32 atoms and of
the four sources of `P₅`, the decomposition of a `GModel` of `P₅` into its four latent
coordinates, and the analytic core of the bilocal inequality. Nothing in it changes any of the
seven statements below, which appear in their original form.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## Auxiliary material -/

namespace FivePathAux

def fiveEquiv : (Bool × Bool × Bool × Bool × Bool) ≃ (Fin 5 → Bool) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  invFun w := (w 0, w 1, w 2, w 3, w 4)
  left_inv p := rfl
  right_inv w := by funext i; fin_cases i <;> rfl

@[simp] theorem fiveEquiv_apply (p : Bool × Bool × Bool × Bool × Bool) :
    fiveEquiv p = ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2] := rfl

theorem sum_five (F : (Fin 5 → Bool) → ℝ) :
    ∑ w : Fin 5 → Bool, F w
      = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool, F ![a,b,c,d,e] := by
  rw [← Equiv.sum_comp fiveEquiv F]
  simp [Fintype.sum_prod_type]

theorem five_ind (q0 q1 q2 q3 q4 : ℝ) (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then
        respMass q0 (w 0) * respMass q1 (w 1) * respMass q2 (w 2) * respMass q3 (w 3) *
          respMass q4 (w 4) else 0)
      = respMass q0 x * respMass q4 z := by
  cases x <;> cases z <;> (rw [sum_five]; simp [respMass]; ring)

theorem five_ind_sgn (q0 q1 q2 q3 q4 : ℝ) (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then
        sgn (w 1) * sgn (w 2) * sgn (w 3) *
          (respMass q0 (w 0) * respMass q1 (w 1) * respMass q2 (w 2) * respMass q3 (w 3) *
            respMass q4 (w 4)) else 0)
      = respMass q0 x * ((2 * q1 - 1) * (2 * q2 - 1) * (2 * q3 - 1)) * respMass q4 z := by
  cases x <;> cases z <;> (rw [sum_five]; simp [respMass, sgn]; ring)


theorem sqrt_cs {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * c) + Real.sqrt (b * d) ≤ Real.sqrt ((a + b) * (c + d)) := by
  have h1 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt (a * d) * Real.sqrt (b * c) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    ring_nf
  have h2 : 2 * (Real.sqrt (a * d) * Real.sqrt (b * c)) ≤ a * d + b * c := by
    have e1 : Real.sqrt (a * d) ^ 2 = a * d := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (b * c))]
  have e3 : Real.sqrt (a * c) ^ 2 = a * c := Real.sq_sqrt (by positivity)
  have e4 : Real.sqrt (b * d) ^ 2 = b * d := Real.sq_sqrt (by positivity)
  have key : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 ≤ (a + b) * (c + d) := by nlinarith
  have hnn : 0 ≤ Real.sqrt (a * c) + Real.sqrt (b * d) := by positivity
  calc Real.sqrt (a * c) + Real.sqrt (b * d)
      = Real.sqrt ((Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((a + b) * (c + d)) := Real.sqrt_le_sqrt key

theorem half_abs_add_le {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |(u + v) / 2| + |(u - v) / 2| ≤ 1 := by
  rcases abs_le.mp hu with ⟨hu1, hu2⟩
  rcases abs_le.mp hv with ⟨hv1, hv2⟩
  rcases abs_cases ((u + v) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((u - v) / 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h1, h2] <;> linarith

variable {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

/-- The analytic core of the bilocal inequality. -/
theorem bilocal_core (ν : Λ → ℝ) (ν' : Λ' → ℝ) (hν : IsLaw ν) (hν' : IsLaw ν')
    (b : Bool → Λ → ℝ) (c : Λ → Λ' → ℝ) (d : Bool → Λ' → ℝ)
    (hb : ∀ x l, |b x l| ≤ 1) (hc : ∀ l r, |c l r| ≤ 1) (hd : ∀ z r, |d z r| ≤ 1)
    (f : Bool → Bool → ℝ)
    (hf : ∀ x z, f x z = ∑ l, ∑ r, ν l * ν' r * (b x l * c l r * d z r)) :
    Real.sqrt |(1/4 : ℝ) * ∑ x : Bool, ∑ z : Bool, f x z|
      + Real.sqrt |(1/4 : ℝ) * ∑ x : Bool, ∑ z : Bool, sgn x * sgn z * f x z| ≤ 1 := by
  classical
  set Bp : Λ → ℝ := fun l => (b false l + b true l) / 2 with hBp
  set Bm : Λ → ℝ := fun l => (b false l - b true l) / 2 with hBm
  set Dp : Λ' → ℝ := fun r => (d false r + d true r) / 2 with hDp
  set Dm : Λ' → ℝ := fun r => (d false r - d true r) / 2 with hDm
  set pp : ℝ := ∑ l, ν l * |Bp l| with hpp
  set pm : ℝ := ∑ l, ν l * |Bm l| with hpm
  set rp : ℝ := ∑ r, ν' r * |Dp r| with hrp
  set rm : ℝ := ∑ r, ν' r * |Dm r| with hrm
  -- the two rewritings
  have hI : (1/4 : ℝ) * ∑ x : Bool, ∑ z : Bool, f x z
      = ∑ l, ∑ r, ν l * ν' r * (Bp l * c l r * Dp r) := by
    simp only [hf, Fintype.sum_bool, Finset.mul_sum, ← Finset.sum_add_distrib, hBp, hDp]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => by ring
  have hJ : (1/4 : ℝ) * ∑ x : Bool, ∑ z : Bool, sgn x * sgn z * f x z
      = ∑ l, ∑ r, ν l * ν' r * (Bm l * c l r * Dm r) := by
    simp only [hf, Fintype.sum_bool, Finset.mul_sum, ← Finset.sum_add_distrib, hBm, hDm, sgn]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => by norm_num; ring
  -- the generic bound
  have bound : ∀ (U : Λ → ℝ) (W : Λ' → ℝ),
      |∑ l, ∑ r, ν l * ν' r * (U l * c l r * W r)|
        ≤ (∑ l, ν l * |U l|) * (∑ r, ν' r * |W r|) := by
    intro U W
    rw [Finset.sum_mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r _ => ?_)
    have h1 : |ν l * ν' r * (U l * c l r * W r)| = ν l * ν' r * (|U l| * |c l r| * |W r|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hν.1 l), abs_of_nonneg (hν'.1 r)]
    rw [h1]
    have h2 : |c l r| ≤ 1 := hc l r
    have hX : 0 ≤ ν l * ν' r * (|U l| * |W r|) :=
      mul_nonneg (mul_nonneg (hν.1 l) (hν'.1 r)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    nlinarith [mul_nonneg hX (sub_nonneg.mpr h2)]
  -- nonnegativity
  have hppz : 0 ≤ pp := Finset.sum_nonneg fun l _ => mul_nonneg (hν.1 l) (abs_nonneg _)
  have hpmz : 0 ≤ pm := Finset.sum_nonneg fun l _ => mul_nonneg (hν.1 l) (abs_nonneg _)
  have hrpz : 0 ≤ rp := Finset.sum_nonneg fun r _ => mul_nonneg (hν'.1 r) (abs_nonneg _)
  have hrmz : 0 ≤ rm := Finset.sum_nonneg fun r _ => mul_nonneg (hν'.1 r) (abs_nonneg _)
  -- the sum bounds
  have hpsum : pp + pm ≤ 1 := by
    rw [hpp, hpm, ← Finset.sum_add_distrib, ← hν.2]
    refine Finset.sum_le_sum fun l _ => ?_
    have := half_abs_add_le (hb false l) (hb true l)
    have h0 := hν.1 l
    nlinarith [abs_nonneg (Bp l), abs_nonneg (Bm l)]
  have hrsum : rp + rm ≤ 1 := by
    rw [hrp, hrm, ← Finset.sum_add_distrib, ← hν'.2]
    refine Finset.sum_le_sum fun r _ => ?_
    have := half_abs_add_le (hd false r) (hd true r)
    have h0 := hν'.1 r
    nlinarith [abs_nonneg (Dp r), abs_nonneg (Dm r)]
  rw [hI, hJ]
  calc Real.sqrt |∑ l, ∑ r, ν l * ν' r * (Bp l * c l r * Dp r)|
        + Real.sqrt |∑ l, ∑ r, ν l * ν' r * (Bm l * c l r * Dm r)|
      ≤ Real.sqrt (pp * rp) + Real.sqrt (pm * rm) :=
        add_le_add (Real.sqrt_le_sqrt (bound _ _)) (Real.sqrt_le_sqrt (bound _ _))
    _ ≤ Real.sqrt ((pp + pm) * (rp + rm)) := sqrt_cs hppz hpmz hrpz hrmz
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 := Real.sqrt_one


def E01 : fivePathGraph.Edge := ⟨s((0 : Fin 5), (1 : Fin 5)), by decide⟩
def E12 : fivePathGraph.Edge := ⟨s((1 : Fin 5), (2 : Fin 5)), by decide⟩
def E23 : fivePathGraph.Edge := ⟨s((2 : Fin 5), (3 : Fin 5)), by decide⟩
def E34 : fivePathGraph.Edge := ⟨s((3 : Fin 5), (4 : Fin 5)), by decide⟩

theorem edge_cases (e : fivePathGraph.Edge) : e = E01 ∨ e = E12 ∨ e = E23 ∨ e = E34 := by
  revert e; decide

theorem edge_univ : (Finset.univ : Finset fivePathGraph.Edge) = {E01, E12, E23, E34} := by decide

theorem inc0 : ∀ e : (fivePathGraph.inc (0 : Fin 5)), e.1 = E01 := by decide
theorem inc1 : ∀ e : (fivePathGraph.inc (1 : Fin 5)), e.1 = E01 ∨ e.1 = E12 := by decide
theorem inc2 : ∀ e : (fivePathGraph.inc (2 : Fin 5)), e.1 = E12 ∨ e.1 = E23 := by decide
theorem inc3 : ∀ e : (fivePathGraph.inc (3 : Fin 5)), e.1 = E23 ∨ e.1 = E34 := by decide
theorem inc4 : ∀ e : (fivePathGraph.inc (4 : Fin 5)), e.1 = E34 := by decide

theorem prod_vert {β : Type*} [CommMonoid β] (g : fivePathGraph.V → β) :
    ∏ v : fivePathGraph.V, g v
      = g (0 : Fin 5) * g (1 : Fin 5) * g (2 : Fin 5) * g (3 : Fin 5) * g (4 : Fin 5) :=
  Fin.prod_univ_five g

theorem prod_edge {β : Type*} [CommMonoid β] (g : fivePathGraph.Edge → β) :
    ∏ e : fivePathGraph.Edge, g e = g E01 * g E12 * g E23 * g E34 := by
  rw [edge_univ, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, mul_assoc, mul_assoc]

variable (M : GModel fivePathGraph)

/-- The latent tuple type of the five-path. -/
abbrev GTup := M.L E01 × M.L E12 × M.L E23 × M.L E34

/-- The latent assignment built from a tuple. -/
def ofTup (p : GTup M) : ∀ e : fivePathGraph.Edge, M.L e :=
  fun e =>
    if h : e = E01 then cast (congrArg M.L h.symm) p.1
    else if h2 : e = E12 then cast (congrArg M.L h2.symm) p.2.1
    else if h3 : e = E23 then cast (congrArg M.L h3.symm) p.2.2.1
    else if h4 : e = E34 then cast (congrArg M.L h4.symm) p.2.2.2
    else absurd (edge_cases e) (by tauto)

@[simp] theorem ofTup_E01 (p : GTup M) : ofTup M p E01 = p.1 := by simp [ofTup]
@[simp] theorem ofTup_E12 (p : GTup M) : ofTup M p E12 = p.2.1 := by
  simp [ofTup, show E12 ≠ E01 by decide]
@[simp] theorem ofTup_E23 (p : GTup M) : ofTup M p E23 = p.2.2.1 := by
  simp [ofTup, show E23 ≠ E01 by decide, show E23 ≠ E12 by decide]
@[simp] theorem ofTup_E34 (p : GTup M) : ofTup M p E34 = p.2.2.2 := by
  simp [ofTup, show E34 ≠ E01 by decide, show E34 ≠ E12 by decide, show E34 ≠ E23 by decide]

/-- Transport an equality of latent assignments along an equality of edges. -/
theorem tup_congr {x y : ∀ e : fivePathGraph.Edge, M.L e} {f g : fivePathGraph.Edge}
    (h : f = g) (hxy : x g = y g) : x f = y f := by subst h; exact hxy

def latEquiv : GTup M ≃ (∀ e : fivePathGraph.Edge, M.L e) where
  toFun := ofTup M
  invFun x := (x E01, x E12, x E23, x E34)
  left_inv p := by simp
  right_inv x := by
    funext e
    rcases edge_cases e with h | h | h | h <;> subst h <;> simp

theorem sum_lat (F : (∀ e : fivePathGraph.Edge, M.L e) → ℝ) :
    ∑ x : (∀ e : fivePathGraph.Edge, M.L e), F x
      = ∑ a : M.L E01, ∑ b : M.L E12, ∑ c : M.L E23, ∑ d : M.L E34,
          F (ofTup M (a, b, c, d)) := by
  rw [← Equiv.sum_comp (latEquiv M) F]
  simp [Fintype.sum_prod_type, latEquiv]

/-- The response at a vertex, as a function of the whole latent tuple. -/
def gResp (v : fivePathGraph.V) (p : GTup M) : ℝ := M.resp v (fun e => ofTup M p e.1)

variable (q : GTup M)

def fA (a : M.L E01) : ℝ := gResp M (0 : Fin 5) (a, q.2.1, q.2.2.1, q.2.2.2)
def fB (a : M.L E01) (b : M.L E12) : ℝ := gResp M (1 : Fin 5) (a, b, q.2.2.1, q.2.2.2)
def fC (b : M.L E12) (c : M.L E23) : ℝ := gResp M (2 : Fin 5) (q.1, b, c, q.2.2.2)
def fD (c : M.L E23) (d : M.L E34) : ℝ := gResp M (3 : Fin 5) (q.1, q.2.1, c, d)
def fE (d : M.L E34) : ℝ := gResp M (4 : Fin 5) (q.1, q.2.1, q.2.2.1, d)

theorem gResp0 (p : GTup M) : gResp M (0 : Fin 5) p = fA M q p.1 := by
  unfold gResp fA; congr 1; funext e
  exact tup_congr M (inc0 e) (by simp)

theorem gResp1 (p : GTup M) : gResp M (1 : Fin 5) p = fB M q p.1 p.2.1 := by
  unfold gResp fB; congr 1; funext e
  rcases inc1 e with h | h <;> exact tup_congr M h (by simp)

theorem gResp2 (p : GTup M) : gResp M (2 : Fin 5) p = fC M q p.2.1 p.2.2.1 := by
  unfold gResp fC; congr 1; funext e
  rcases inc2 e with h | h <;> exact tup_congr M h (by simp)

theorem gResp3 (p : GTup M) : gResp M (3 : Fin 5) p = fD M q p.2.2.1 p.2.2.2 := by
  unfold gResp fD; congr 1; funext e
  rcases inc3 e with h | h <;> exact tup_congr M h (by simp)

theorem gResp4 (p : GTup M) : gResp M (4 : Fin 5) p = fE M q p.2.2.2 := by
  unfold gResp fE; congr 1; funext e
  exact tup_congr M (inc4 e) (by simp)

theorem law_eq (w : fivePathGraph.V → Bool) :
    M.law w = ∑ a : M.L E01, ∑ b : M.L E12, ∑ c : M.L E23, ∑ d : M.L E34,
      (M.μ E01 a * M.μ E12 b * M.μ E23 c * M.μ E34 d) *
        (respMass (fA M q a) (w (0 : Fin 5)) * respMass (fB M q a b) (w (1 : Fin 5)) *
          respMass (fC M q b c) (w (2 : Fin 5)) * respMass (fD M q c d) (w (3 : Fin 5)) *
          respMass (fE M q d) (w (4 : Fin 5))) := by
  unfold GModel.law
  rw [sum_lat]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [prod_edge, prod_vert]
  have h0 : M.resp (0 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fA M q a :=
    gResp0 M q (a, b, c, d)
  have h1 : M.resp (1 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fB M q a b :=
    gResp1 M q (a, b, c, d)
  have h2 : M.resp (2 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fC M q b c :=
    gResp2 M q (a, b, c, d)
  have h3 : M.resp (3 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fD M q c d :=
    gResp3 M q (a, b, c, d)
  have h4 : M.resp (4 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fE M q d :=
    gResp4 M q (a, b, c, d)
  rw [h0, h1, h2, h3, h4]
  simp


theorem cell_step (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then M.law w else 0)
      = ∑ X : (∀ e : fivePathGraph.Edge, M.L e), (∏ e, M.μ e (X e)) *
          (respMass (M.resp (0 : Fin 5) fun e => X e.1) x *
            respMass (M.resp (4 : Fin 5) fun e => X e.1) z) := by
  have hstep : ∀ w : Fin 5 → Bool, (if w 0 = x ∧ w 4 = z then M.law w else 0)
      = ∑ X : (∀ e : fivePathGraph.Edge, M.L e),
          (if w 0 = x ∧ w 4 = z then
            (∏ e, M.μ e (X e)) * ∏ v, respMass (M.resp v fun e => X e.1) (w v) else 0) := by
    intro w
    by_cases hcond : w 0 = x ∧ w 4 = z
    · simp only [ite_eq_left hcond]; rfl
    · simp only [ite_eq_right hcond, Finset.sum_const_zero]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  have hpull : ∀ w : Fin 5 → Bool,
      (if w 0 = x ∧ w 4 = z then
          (∏ e, M.μ e (X e)) * ∏ v, respMass (M.resp v fun e => X e.1) (w v) else 0)
        = (∏ e, M.μ e (X e)) *
            (if w 0 = x ∧ w 4 = z then ∏ v, respMass (M.resp v fun e => X e.1) (w v) else 0) := by
    intro w; by_cases hcond : w 0 = x ∧ w 4 = z <;> simp [hcond]
  simp only [hpull, ← Finset.mul_sum]
  congr 1
  simp only [prod_vert]
  exact five_ind _ _ _ _ _ x z

theorem num_step (x z : Bool) :
    (∑ w : Fin 5 → Bool,
        if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * M.law w else 0)
      = ∑ X : (∀ e : fivePathGraph.Edge, M.L e), (∏ e, M.μ e (X e)) *
          (respMass (M.resp (0 : Fin 5) fun e => X e.1) x *
            ((2 * M.resp (1 : Fin 5) (fun e => X e.1) - 1) *
              (2 * M.resp (2 : Fin 5) (fun e => X e.1) - 1) *
              (2 * M.resp (3 : Fin 5) (fun e => X e.1) - 1)) *
            respMass (M.resp (4 : Fin 5) fun e => X e.1) z) := by
  have hstep : ∀ w : Fin 5 → Bool,
      (if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * M.law w else 0)
      = ∑ X : (∀ e : fivePathGraph.Edge, M.L e),
          (if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) *
            ((∏ e, M.μ e (X e)) * ∏ v, respMass (M.resp v fun e => X e.1) (w v)) else 0) := by
    intro w
    by_cases hcond : w 0 = x ∧ w 4 = z
    · simp only [ite_eq_left hcond]
      have hl : M.law w = ∑ X : (∀ e : fivePathGraph.Edge, M.L e), (∏ e, M.μ e (X e)) *
          ∏ v, respMass (M.resp v fun e => X e.1) (w v) := rfl
      rw [hl, Finset.mul_sum]
    · simp only [ite_eq_right hcond, Finset.sum_const_zero]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  have hpull : ∀ w : Fin 5 → Bool,
      (if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) *
          ((∏ e, M.μ e (X e)) * ∏ v, respMass (M.resp v fun e => X e.1) (w v)) else 0)
        = (∏ e, M.μ e (X e)) *
            (if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) *
              (∏ v, respMass (M.resp v fun e => X e.1) (w v)) else 0) := by
    intro w; by_cases hcond : w 0 = x ∧ w 4 = z <;> simp [hcond] <;> ring
  simp only [hpull, ← Finset.mul_sum]
  congr 1
  simp only [prod_vert]
  exact five_ind_sgn _ _ _ _ _ x z

theorem respMass_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (b : Bool) : 0 ≤ respMass r b := by
  cases b <;> simp [respMass] <;> linarith

theorem sgnResp_abs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : |2 * r - 1| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

/-- Factoring a four-fold latent sum whose summand depends only on the outer coordinates. -/
theorem sum4_factor {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ) (F : A → ℝ) (K : D → ℝ)
    (hg : ∑ b, g b = 1) (hh : ∑ c, h c = 1) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a * g b * h c * k d) * (F a * K d))
      = (∑ a, f a * F a) * (∑ d, k d * K d) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have inner : ∀ b c, (∑ d, (f a * g b * h c * k d) * (F a * K d))
      = (g b * h c) * ∑ d, (f a * F a) * (k d * K d) := by
    intro b c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [inner, ← Finset.sum_mul, ← Finset.sum_mul_sum, hg, hh, one_mul]

/-- Factoring a four-fold latent sum with a chain-shaped summand. -/
theorem sum4_chain {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ) (F : A → ℝ) (K : D → ℝ)
    (BB : A → B → ℝ) (CC : B → C → ℝ) (DD : C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a * g b * h c * k d) * (F a * (BB a b * CC b c * DD c d) * K d))
      = ∑ b, ∑ c, g b * h c *
          ((∑ a, f a * F a * BB a b) * CC b c * (∑ d, k d * K d * DD c d)) := by
  have step1 : ∀ a b c, (∑ d, (f a * g b * h c * k d) * (F a * (BB a b * CC b c * DD c d) * K d))
      = (f a * F a * BB a b) * (g b * h c * CC b c) * (∑ d, k d * K d * DD c d) := by
    intro a b c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem cell_eq (hM : M.Valid) (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then M.law w else 0)
      = (∑ a, M.μ E01 a * respMass (fA M q a) x) * (∑ d, M.μ E34 d * respMass (fE M q d) z) := by
  rw [cell_step, sum_lat]
  have hrw : ∀ (a : M.L E01) (b : M.L E12) (c : M.L E23) (d : M.L E34),
      (∏ e, M.μ e (ofTup M (a, b, c, d) e)) *
          (respMass (M.resp (0 : Fin 5) fun e => ofTup M (a, b, c, d) e.1) x *
            respMass (M.resp (4 : Fin 5) fun e => ofTup M (a, b, c, d) e.1) z)
        = (M.μ E01 a * M.μ E12 b * M.μ E23 c * M.μ E34 d) *
            (respMass (fA M q a) x * respMass (fE M q d) z) := by
    intro a b c d
    rw [prod_edge,
      show M.resp (0 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fA M q a from
        gResp0 M q (a, b, c, d),
      show M.resp (4 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fE M q d from
        gResp4 M q (a, b, c, d)]
    simp
  simp only [hrw]
  exact sum4_factor _ _ _ _ _ _ (hM.1 E12).2 (hM.1 E23).2

theorem num_eq (x z : Bool) :
    (∑ w : Fin 5 → Bool,
        if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * M.law w else 0)
      = ∑ b, ∑ c, M.μ E12 b * M.μ E23 c *
          ((∑ a, M.μ E01 a * respMass (fA M q a) x * (2 * fB M q a b - 1)) *
            (2 * fC M q b c - 1) *
            (∑ d, M.μ E34 d * respMass (fE M q d) z * (2 * fD M q c d - 1))) := by
  rw [num_step, sum_lat]
  have hrw : ∀ (a : M.L E01) (b : M.L E12) (c : M.L E23) (d : M.L E34),
      (∏ e, M.μ e (ofTup M (a, b, c, d) e)) *
          (respMass (M.resp (0 : Fin 5) fun e => ofTup M (a, b, c, d) e.1) x *
            ((2 * M.resp (1 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) - 1) *
              (2 * M.resp (2 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) - 1) *
              (2 * M.resp (3 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) - 1)) *
            respMass (M.resp (4 : Fin 5) fun e => ofTup M (a, b, c, d) e.1) z)
        = (M.μ E01 a * M.μ E12 b * M.μ E23 c * M.μ E34 d) *
            (respMass (fA M q a) x *
              ((2 * fB M q a b - 1) * (2 * fC M q b c - 1) * (2 * fD M q c d - 1)) *
              respMass (fE M q d) z) := by
    intro a b c d
    rw [prod_edge,
      show M.resp (0 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fA M q a from
        gResp0 M q (a, b, c, d),
      show M.resp (1 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fB M q a b from
        gResp1 M q (a, b, c, d),
      show M.resp (2 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fC M q b c from
        gResp2 M q (a, b, c, d),
      show M.resp (3 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fD M q c d from
        gResp3 M q (a, b, c, d),
      show M.resp (4 : Fin 5) (fun e => ofTup M (a, b, c, d) e.1) = fE M q d from
        gResp4 M q (a, b, c, d)]
    simp
  simp only [hrw]
  exact sum4_chain _ _ _ _ _ _ _ _ _

theorem wsum_abs_le {A : Type} [Fintype A] (f : A → ℝ) (g : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hg : ∀ a, |g a| ≤ 1) : |∑ a, f a * g a| ≤ ∑ a, f a := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_of_nonneg (hf a)]
  nlinarith [hf a, abs_nonneg (g a), hg a]

theorem latent_nonempty (hM : M.Valid) (e : fivePathGraph.Edge) : Nonempty (M.L e) := by
  by_contra hn
  rw [not_nonempty_iff] at hn
  have h := (hM.1 e).2
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h
  exact zero_ne_one h

/-- The endpoint weight `Pr(A = x)` of the model. -/
def alphaW (x : Bool) : ℝ := ∑ a, M.μ E01 a * respMass (fA M q a) x

/-- The endpoint weight `Pr(E = z)` of the model. -/
def epsiW (z : Bool) : ℝ := ∑ d, M.μ E34 d * respMass (fE M q d) z

/-- The unnormalized conditional response of `B`. -/
def betaW (x : Bool) (b : M.L E12) : ℝ :=
  ∑ a, M.μ E01 a * respMass (fA M q a) x * (2 * fB M q a b - 1)

/-- The unnormalized conditional response of `D`. -/
def deltaW (z : Bool) (c : M.L E23) : ℝ :=
  ∑ d, M.μ E34 d * respMass (fE M q d) z * (2 * fD M q c d - 1)

theorem cell_eq' (hM : M.Valid) (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then M.law w else 0)
      = alphaW M q x * epsiW M q z := cell_eq M q hM x z

theorem num_eq' (x z : Bool) :
    (∑ w : Fin 5 → Bool,
        if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * M.law w else 0)
      = ∑ b, ∑ c, M.μ E12 b * M.μ E23 c *
          (betaW M q x b * (2 * fC M q b c - 1) * deltaW M q z c) := num_eq M q x z

/-! ### The explicit target -/

theorem fivePathTarget_ge (h : ℝ) (hh : 0 ≤ h) (w : Fin 5 → Bool) :
    (1 - h) / 64 ≤ fivePathTarget h w := by
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;> cases h4 : w 4 <;>
    simp [fivePathTarget, sgn, h0, h1, h2, h3, h4] <;> linarith

theorem target_sum (h : ℝ) : ∑ w : Fin 5 → Bool, fivePathTarget h w = 1 := by
  rw [sum_five]; simp [fivePathTarget, sgn]; ring

theorem target_cell (h : ℝ) (x z : Bool) :
    (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then fivePathTarget h w else 0) = 1 / 4 := by
  cases x <;> cases z <;> (rw [sum_five]; simp [fivePathTarget, sgn]; ring)

theorem target_num (h : ℝ) (x z : Bool) :
    (∑ w : Fin 5 → Bool,
        if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * fivePathTarget h w else 0)
      = (1 / 4) * ((1 + h) / 4 * (1 + sgn x * sgn z)) := by
  cases x <;> cases z <;> (rw [sum_five]; simp [fivePathTarget, sgn]; try ring)

theorem target_corr (h : ℝ) (x z : Bool) :
    fivePathCorr (fivePathTarget h) x z = (1 + h) / 4 * (1 + sgn x * sgn z) := by
  have hdef : fivePathCorr (fivePathTarget h) x z =
      (∑ w : Fin 5 → Bool,
          if w 0 = x ∧ w 4 = z then
            sgn (w 1) * sgn (w 2) * sgn (w 3) * fivePathTarget h w else 0) /
        (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then fivePathTarget h w else 0) := rfl
  rw [hdef, target_num, target_cell]
  ring

/-! ### Laws of models, and a compatible law -/

theorem five_tot (q0 q1 q2 q3 q4 : ℝ) :
    (∑ w : Fin 5 → Bool, respMass q0 (w 0) * respMass q1 (w 1) * respMass q2 (w 2) *
      respMass q3 (w 3) * respMass q4 (w 4)) = 1 := by
  rw [sum_five]; simp [respMass]; ring

theorem sum4_one {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ)
    (hf : ∑ a, f a = 1) (hg : ∑ b, g b = 1) (hh : ∑ c, h c = 1) (hk : ∑ d, k d = 1) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a * g b * h c * k d) = 1 := by
  have e1 : ∀ a b c, (∑ d, f a * g b * h c * k d) = f a * g b * h c := by
    intro a b c; rw [← Finset.mul_sum, hk, mul_one]
  simp only [e1]
  have e2 : ∀ a b, (∑ c, f a * g b * h c) = f a * g b := by
    intro a b; rw [← Finset.mul_sum, hh, mul_one]
  simp only [e2]
  have e3 : ∀ a, (∑ b, f a * g b) = f a := by
    intro a; rw [← Finset.mul_sum, hg, mul_one]
  simp only [e3]
  exact hf

theorem model_isLaw (hM : M.Valid) : IsLaw M.law := by
  refine ⟨fun w => ?_, ?_⟩
  · refine Finset.sum_nonneg fun X _ =>
      mul_nonneg (Finset.prod_nonneg fun e _ => (hM.1 e).1 _)
        (Finset.prod_nonneg fun v _ => respMass_nonneg (hM.2 _ _).1 (hM.2 _ _).2 _)
  · change (∑ w : Fin 5 → Bool, M.law w) = 1
    have hstep : ∀ w : Fin 5 → Bool, M.law w
        = ∑ X : (∀ e : fivePathGraph.Edge, M.L e), (∏ e, M.μ e (X e)) *
            ∏ v, respMass (M.resp v fun e => X e.1) (w v) := fun w => rfl
    simp only [hstep]
    rw [Finset.sum_comm]
    have hinner : ∀ X : (∀ e : fivePathGraph.Edge, M.L e),
        (∑ w : Fin 5 → Bool, (∏ e, M.μ e (X e)) *
            ∏ v, respMass (M.resp v fun e => X e.1) (w v)) = ∏ e, M.μ e (X e) := by
      intro X
      rw [← Finset.mul_sum]
      simp only [prod_vert]
      rw [five_tot, mul_one]
    simp only [hinner]
    rw [sum_lat]
    simp only [prod_edge, ofTup_E01, ofTup_E12, ofTup_E23, ofTup_E34]
    exact sum4_one _ _ _ _ (hM.1 E01).2 (hM.1 E12).2 (hM.1 E23).2 (hM.1 E34).2

/-- The five-path model with trivial sources and fair responses. -/
noncomputable def trivModel : GModel fivePathGraph where
  L := fun _ => Unit
  fintypeL := fun _ => inferInstance
  μ := fun _ _ => 1
  resp := fun _ _ => 1 / 2

theorem trivModel_valid : trivModel.Valid := by
  refine ⟨fun e => ⟨fun a => ?_, ?_⟩, fun v c => ?_⟩
  · change (0 : ℝ) ≤ 1; norm_num
  · change (∑ _a : Unit, (1 : ℝ)) = 1; simp
  · change (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1; norm_num

theorem exists_compatible : ∃ Q : GTarget fivePathGraph, GCompatible fivePathGraph Q :=
  ⟨trivModel.law, trivModel, trivModel_valid, rfl⟩

/-- A conditional-cell functional moves by at most twice the total variation distance. -/
theorem tv_bound (P Q G : (Fin 5 → Bool) → ℝ) (hG : ∀ w, |G w| ≤ 1) (x z : Bool) :
    |(∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then G w * Q w else 0)
        - (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then G w * P w else 0)|
      ≤ 2 * dTV P Q := by
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ w : Fin 5 → Bool,
      ((if w 0 = x ∧ w 4 = z then G w * Q w else 0) - if w 0 = x ∧ w 4 = z then G w * P w else 0)
        = if w 0 = x ∧ w 4 = z then G w * (Q w - P w) else 0 := by
    intro w; by_cases hcond : w 0 = x ∧ w 4 = z <;> simp [hcond] <;> ring
  simp only [hterm]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hbd : ∀ w : Fin 5 → Bool,
      |if w 0 = x ∧ w 4 = z then G w * (Q w - P w) else 0| ≤ |P w - Q w| := by
    intro w
    by_cases hcond : w 0 = x ∧ w 4 = z
    · rw [ite_eq_left hcond, abs_mul, ← abs_neg (Q w - P w), neg_sub]
      nlinarith [abs_nonneg (G w), abs_nonneg (P w - Q w), hG w]
    · rw [ite_eq_right hcond, abs_zero]; exact abs_nonneg _
  refine le_trans (Finset.sum_le_sum fun w _ => hbd w) ?_
  rw [dTV]
  ring_nf
  rfl

theorem sgn3_abs_le (w : Fin 5 → Bool) : |sgn (w 1) * sgn (w 2) * sgn (w 3)| ≤ 1 := by
  cases w 1 <;> cases w 2 <;> cases w 3 <;> simp [sgn]

theorem dTV_nonneg {α : Type*} [Fintype α] (P Q : α → ℝ) : 0 ≤ dTV P Q := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => abs_nonneg _)

theorem tv_cell (P Q : (Fin 5 → Bool) → ℝ) (x z : Bool) :
    |(∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then Q w else 0)
        - (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then P w else 0)| ≤ 2 * dTV P Q := by
  have h := tv_bound P Q (fun _ => 1) (by intro w; norm_num) x z
  simpa using h

theorem tv_num (P Q : (Fin 5 → Bool) → ℝ) (x z : Bool) :
    |(∑ w : Fin 5 → Bool,
          if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * Q w else 0)
        - (∑ w : Fin 5 → Bool,
          if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * P w else 0)|
      ≤ 2 * dTV P Q :=
  tv_bound P Q (fun w => sgn (w 1) * sgn (w 2) * sgn (w 3)) sgn3_abs_le x z

theorem fivePathI_expand (R : (Fin 5 → Bool) → ℝ) :
    fivePathI R = (1 / 4) * (fivePathCorr R false false + fivePathCorr R false true +
      (fivePathCorr R true false + fivePathCorr R true true)) := by
  simp [fivePathI]
  ring

theorem fivePathJ_expand (R : (Fin 5 → Bool) → ℝ) :
    fivePathJ R = (1 / 4) * (fivePathCorr R false false - fivePathCorr R false true +
      (-fivePathCorr R true false + fivePathCorr R true true)) := by
  simp [fivePathJ, sgn]
  ring

theorem targetCorr_bounds (h : ℝ) (h1 : h < 1) (h0 : 0 ≤ h) (x z : Bool) :
    0 ≤ (1 + h) / 4 * (1 + sgn x * sgn z) ∧ (1 + h) / 4 * (1 + sgn x * sgn z) ≤ 1 := by
  have hs : sgn x * sgn z = 1 ∨ sgn x * sgn z = -1 := by
    cases x <;> cases z <;> norm_num [sgn]
  rcases hs with hs | hs <;> rw [hs] <;> constructor <;> linarith

theorem sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end FivePathAux

open FivePathAux

/-! ## A4: the five-observer path -/

/-- AUDIT-NOTES A4, the bilocal inequality for the five-path. For a compatible law with
positive endpoint cells, `√|I| + √|J| ≤ 1`. Conditioning on `A = x` and `E = z` changes only
the endpoint source laws and leaves `L`, `R` independent; with
`p_± = E_L|(b_0 ± b_1)/2|` and `r_± = E_R|(d_0 ± d_1)/2|` one has `p_+ + p_- ≤ 1`,
`r_+ + r_- ≤ 1`, `|I| ≤ p_+ r_+`, `|J| ≤ p_- r_-`, and Cauchy–Schwarz finishes. -/
theorem bilocal_of_compatible (P : GTarget fivePathGraph) (hP : IsLaw P)
    (hc : GCompatible fivePathGraph P)
    (hcell : ∀ x z : Bool, 0 < ∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then P w else 0) :
    Real.sqrt |fivePathI P| + Real.sqrt |fivePathJ P| ≤ 1 := by
  obtain ⟨M, hM, hMP⟩ := hc
  subst hMP
  obtain ⟨a0⟩ := latent_nonempty M hM E01
  obtain ⟨b0⟩ := latent_nonempty M hM E12
  obtain ⟨c0⟩ := latent_nonempty M hM E23
  obtain ⟨d0⟩ := latent_nonempty M hM E34
  have hwA : ∀ (x : Bool) (a : M.L E01),
      0 ≤ M.μ E01 a * respMass (fA M (a0, b0, c0, d0) a) x := fun x a =>
    mul_nonneg ((hM.1 E01).1 a) (respMass_nonneg (hM.2 _ _).1 (hM.2 _ _).2 x)
  have hwE : ∀ (z : Bool) (d : M.L E34),
      0 ≤ M.μ E34 d * respMass (fE M (a0, b0, c0, d0) d) z := fun z d =>
    mul_nonneg ((hM.1 E34).1 d) (respMass_nonneg (hM.2 _ _).1 (hM.2 _ _).2 z)
  have halnn : ∀ x, 0 ≤ alphaW M (a0, b0, c0, d0) x := fun x =>
    Finset.sum_nonneg fun a _ => hwA x a
  have hepnn : ∀ z, 0 ≤ epsiW M (a0, b0, c0, d0) z := fun z =>
    Finset.sum_nonneg fun d _ => hwE z d
  have hcellprod : ∀ x z : Bool,
      0 < alphaW M (a0, b0, c0, d0) x * epsiW M (a0, b0, c0, d0) z := by
    intro x z
    have h := hcell x z
    rwa [cell_eq' M (a0, b0, c0, d0) hM x z] at h
  have halpos : ∀ x, 0 < alphaW M (a0, b0, c0, d0) x := by
    intro x
    rcases lt_or_eq_of_le (halnn x) with h | h
    · exact h
    · exact absurd (hcellprod x false) (by rw [← h]; simp)
  have heppos : ∀ z, 0 < epsiW M (a0, b0, c0, d0) z := by
    intro z
    rcases lt_or_eq_of_le (hepnn z) with h | h
    · exact h
    · exact absurd (hcellprod false z) (by rw [← h]; simp)
  have hbeabs : ∀ x b, |betaW M (a0, b0, c0, d0) x b| ≤ alphaW M (a0, b0, c0, d0) x := fun x b =>
    wsum_abs_le _ _ (hwA x) (fun a => sgnResp_abs_le (hM.2 _ _).1 (hM.2 _ _).2)
  have hdeabs : ∀ z c, |deltaW M (a0, b0, c0, d0) z c| ≤ epsiW M (a0, b0, c0, d0) z := fun z c =>
    wsum_abs_le _ _ (hwE z) (fun d => sgnResp_abs_le (hM.2 _ _).1 (hM.2 _ _).2)
  have hcorr : ∀ x z : Bool, fivePathCorr M.law x z
      = ∑ b, ∑ c, M.μ E12 b * M.μ E23 c *
          (betaW M (a0, b0, c0, d0) x b / alphaW M (a0, b0, c0, d0) x *
            (2 * fC M (a0, b0, c0, d0) b c - 1) *
            (deltaW M (a0, b0, c0, d0) z c / epsiW M (a0, b0, c0, d0) z)) := by
    intro x z
    have hdef : fivePathCorr M.law x z =
        (∑ w : Fin 5 → Bool,
            if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * M.law w else 0) /
          (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then M.law w else 0) := rfl
    rw [hdef, num_eq' M (a0, b0, c0, d0) x z, cell_eq' M (a0, b0, c0, d0) hM x z,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : alphaW M (a0, b0, c0, d0) x ≠ 0 := ne_of_gt (halpos x)
    have h2 : epsiW M (a0, b0, c0, d0) z ≠ 0 := ne_of_gt (heppos z)
    field_simp
  have hbb : ∀ (x : Bool) (l : M.L E12),
      |betaW M (a0, b0, c0, d0) x l / alphaW M (a0, b0, c0, d0) x| ≤ 1 := by
    intro x l
    rw [abs_div, abs_of_pos (halpos x), div_le_one (halpos x)]
    exact hbeabs x l
  have hdd : ∀ (z : Bool) (r : M.L E23),
      |deltaW M (a0, b0, c0, d0) z r / epsiW M (a0, b0, c0, d0) z| ≤ 1 := by
    intro z r
    rw [abs_div, abs_of_pos (heppos z), div_le_one (heppos z)]
    exact hdeabs z r
  exact bilocal_core (M.μ E12) (M.μ E23) (hM.1 E12) (hM.1 E23)
    (fun x l => betaW M (a0, b0, c0, d0) x l / alphaW M (a0, b0, c0, d0) x)
    (fun b c => 2 * fC M (a0, b0, c0, d0) b c - 1)
    (fun z r => deltaW M (a0, b0, c0, d0) z r / epsiW M (a0, b0, c0, d0) z)
    hbb (fun l r => sgnResp_abs_le (hM.2 _ _).1 (hM.2 _ _).2) hdd
    (fivePathCorr M.law) hcorr

/-- The five-path target is a law, and is bounded below by `(1−h)/64` at every atom
(AUDIT-NOTES A4, packet equation (8)). -/
theorem fivePathTarget_isLaw (h : ℝ) (h0 : 0 ≤ h) (h1 : h < 1) :
    IsLaw (fivePathTarget h) ∧ ∀ w, (1 - h) / 64 ≤ fivePathTarget h w := by
  refine ⟨⟨fun w => le_trans ?_ (fivePathTarget_ge h h0 w), target_sum h⟩, fivePathTarget_ge h h0⟩
  linarith

/-- AUDIT-NOTES A4, the correlators of the target: `f_{xz} = (1+h)/2` when `x = z` and `0`
otherwise, so `I = J = (1+h)/4`. -/
theorem fivePathTarget_corr (h : ℝ) (h0 : 0 ≤ h) (h1 : h < 1) :
    fivePathI (fivePathTarget h) = (1 + h) / 4 ∧ fivePathJ (fivePathTarget h) = (1 + h) / 4 := by
  constructor
  · change (1 / 4 : ℝ) * ∑ x : Bool, ∑ z : Bool, fivePathCorr (fivePathTarget h) x z = _
    simp [target_corr, sgn]
    ring
  · change (1 / 4 : ℝ) * ∑ x : Bool, ∑ z : Bool,
      sgn x * sgn z * fivePathCorr (fivePathTarget h) x z = _
    simp [target_corr, sgn]
    ring

/-- AUDIT-NOTES A4: the five-path target is incompatible for every `0 < h < 1`, since
`√I + √J = √(1+h) > 1` contradicts the bilocal inequality. (Finite-latent compatible set;
see the header.) -/
theorem fivePath_not_compatible (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    ¬ GCompatible fivePathGraph (fivePathTarget h) := by
  intro hc
  have hlaw := (fivePathTarget_isLaw h h0.le h1).1
  have hcellpos : ∀ x z : Bool,
      0 < ∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then fivePathTarget h w else 0 := by
    intro x z; rw [target_cell]; norm_num
  have hb := bilocal_of_compatible (fivePathTarget h) hlaw hc hcellpos
  obtain ⟨hI, hJ⟩ := fivePathTarget_corr h h0.le h1
  rw [hI, hJ, abs_of_nonneg (by linarith : (0:ℝ) ≤ (1 + h) / 4)] at hb
  have hnn : (0:ℝ) ≤ (1 + h) / 4 := by linarith
  have hsq := Real.sq_sqrt hnn
  have hpos := Real.sqrt_nonneg ((1 + h) / 4)
  nlinarith

/-- AUDIT-NOTES A4 with the corrected constant. The packet states `d_TV ≥ h/16`; the argument
as written gives `|I_R − I_P|, |J_R − J_P| ≤ 24 d` for `d < 1/8`, so the safe constant is
`h/96`. At `h_t = 1/(16t²)` this is `1/(1536 t²)`. -/
theorem fivePath_distance (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    h / 96 ≤ distToCompatible fivePathGraph (fivePathTarget h) := by
  change h / 96 ≤ sInf {d : ℝ | ∃ Q : GTarget fivePathGraph,
    GCompatible fivePathGraph Q ∧ d = dTV (fivePathTarget h) Q}
  refine le_csInf ?_ ?_
  · obtain ⟨Q, hQ⟩ := exists_compatible
    exact ⟨dTV (fivePathTarget h) Q, Q, hQ, rfl⟩
  · rintro dd ⟨Q, hQ, rfl⟩
    by_contra hcon
    rw [not_le] at hcon
    have hd0 : 0 ≤ dTV (fivePathTarget h) Q := dTV_nonneg _ _
    set d : ℝ := dTV (fivePathTarget h) Q with hdd
    have hdsmall : d < h / 96 := hcon
    have hdlt : d < 1 / 96 := by
      have : h / 96 < 1 / 96 := by linarith
      linarith
    obtain ⟨M, hM, hMQ⟩ := hQ
    have hQlaw : IsLaw Q := hMQ ▸ model_isLaw M hM
    -- cells of `Q`
    have hcellQ : ∀ x z : Bool,
        (1 : ℝ) / 5 < ∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then Q w else 0 := by
      intro x z
      have hb := tv_cell (fivePathTarget h) Q x z
      rw [target_cell] at hb
      rcases abs_le.mp hb with ⟨hb1, hb2⟩
      linarith
    -- the correlators move little
    have hcorrdiff : ∀ x z : Bool,
        |fivePathCorr Q x z - fivePathCorr (fivePathTarget h) x z| ≤ 20 * d := by
      intro x z
      set A : ℝ := ∑ w : Fin 5 → Bool,
        if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * Q w else 0 with hA
      set B : ℝ := ∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then Q w else 0 with hB
      set NP : ℝ := (1 + h) / 4 * (1 + sgn x * sgn z) with hNP
      have hBpos : (1 : ℝ) / 5 < B := hcellQ x z
      have hBp : 0 < B := by linarith
      have hAb : |A - NP / 4| ≤ 2 * d := by
        have hb := tv_num (fivePathTarget h) Q x z
        rw [target_num] at hb
        have he : (1 / 4 : ℝ) * ((1 + h) / 4 * (1 + sgn x * sgn z)) = NP / 4 := by
          rw [hNP]; ring
        rw [he] at hb
        exact hb
      have hBb : |B - 1 / 4| ≤ 2 * d := by
        have hb := tv_cell (fivePathTarget h) Q x z
        rw [target_cell] at hb
        exact hb
      obtain ⟨hNP0, hNP1⟩ := targetCorr_bounds h h1 h0.le x z
      have hcQ : fivePathCorr Q x z = A / B := rfl
      have hcP : fivePathCorr (fivePathTarget h) x z = NP := target_corr h x z
      rw [hcQ, hcP]
      have key : A / B - NP = (A - NP * B) / B := by field_simp
      rw [key, abs_div, abs_of_pos hBp, div_le_iff₀ hBp]
      have h4 : |A - NP * B| ≤ 4 * d := by
        rcases abs_le.mp hAb with ⟨ha1, ha2⟩
        rcases abs_le.mp hBb with ⟨hb1, hb2⟩
        rw [abs_le]
        constructor
        · nlinarith [mul_nonneg hNP0 (sub_nonneg.mpr hb2)]
        · nlinarith [mul_nonneg hNP0 (sub_nonneg.mpr hb2)]
      nlinarith
    -- the two combinations stay above 1/4
    have hIb : (1 : ℝ) / 4 < fivePathI Q := by
      have e1 := abs_le.mp (hcorrdiff false false)
      have e2 := abs_le.mp (hcorrdiff false true)
      have e3 := abs_le.mp (hcorrdiff true false)
      have e4 := abs_le.mp (hcorrdiff true true)
      have ht : fivePathI (fivePathTarget h) = (1 + h) / 4 :=
        (fivePathTarget_corr h h0.le h1).1
      have hexp := fivePathI_expand Q
      rw [fivePathI_expand] at ht
      rw [hexp]
      linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
    have hJb : (1 : ℝ) / 4 < fivePathJ Q := by
      have e1 := abs_le.mp (hcorrdiff false false)
      have e2 := abs_le.mp (hcorrdiff false true)
      have e3 := abs_le.mp (hcorrdiff true false)
      have e4 := abs_le.mp (hcorrdiff true true)
      have ht : fivePathJ (fivePathTarget h) = (1 + h) / 4 :=
        (fivePathTarget_corr h h0.le h1).2
      have hexp := fivePathJ_expand Q
      rw [fivePathJ_expand] at ht
      rw [hexp]
      linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
    -- contradiction with the bilocal inequality
    have hbil := bilocal_of_compatible Q hQlaw ⟨M, hM, hMQ⟩
      (fun x z => lt_trans (by norm_num) (hcellQ x z))
    have hI2 : (1 : ℝ) / 2 < Real.sqrt |fivePathI Q| := by
      rw [← sqrt_quarter]
      refine Real.sqrt_lt_sqrt (by norm_num) ?_
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ fivePathI Q)]
      linarith
    have hJ2 : (1 : ℝ) / 2 < Real.sqrt |fivePathJ Q| := by
      rw [← sqrt_quarter]
      refine Real.sqrt_lt_sqrt (by norm_num) ?_
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ fivePathJ Q)]
      linarith
    linarith


end TriangleInflation.Graph
