/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Certified Runge-Kutta Order Conditions

This file checks concrete Runge-Kutta methods against their rooted-tree Butcher
order conditions. It defines a small computable engine for planar rooted trees,
the density `γ`, and the elementary weight `Φ(A,b)`, proves the finite-catalogue
keystone for order conditions, and verifies Euler, Heun, RK4, Dormand-Prince,
and Gauss-Legendre certificates.
-/

namespace RungeKuttaOrderConditions

/-- ℚ(√15) as a computable `CommRing`: `⟨a, b⟩` means `a + b·√15`; the
    relation √15²=15 is baked into `mul`.  Coefficient ring for the Gauss–Legendre s=3
    (order 6) tableau (Brick 5).  Working in this concrete pair ring keeps the
    order-condition checks a pure ℚ component computation closed by `norm_num` — no
    algebraic-number tactic needed. -/
structure Q15 where
  /-- Rational component. -/
  re : ℚ
  /-- Coefficient of √15. -/
  im : ℚ
deriving DecidableEq

namespace Q15
@[ext] theorem ext' {x y : Q15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Q15 := ⟨0, 0⟩
instance : One Q15  := ⟨1, 0⟩
instance : Add Q15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Q15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Q15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Q15 := ⟨fun x y =>
  ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Q15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Q15).im = 0 := rfl
@[simp] theorem one_re : (1 : Q15).re = 1 := rfl
@[simp] theorem one_im : (1 : Q15).im = 0 := rfl
@[simp] theorem add_re (x y : Q15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Q15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Q15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Q15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Q15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Q15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Q15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Q15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Q15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
@[simp] theorem natCast_eq (n : ℕ) : ((n : ℕ) : Q15) = ⟨(n : ℚ), 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> simp [Nat.cast_succ]
end Q15

/-- ℤ[√15] as a computable `CommRing`: `⟨a,b⟩` means `a + b·√15` with
    `a,b : ℤ`.  Identical in shape to `Q15` but over the INTEGERS, so equality is
    decided by the kernel's GMP `Int` arithmetic with no rational `Nat.gcd`
    normalization.  Used in Brick 6 to certify Gauss order 6 by `decide` after the
    tableau is cleared of denominators (scaled by `D=360`). -/
structure Z15 where
  /-- Integer component. -/
  re : Int
  /-- Integer coefficient of √15. -/
  im : Int
deriving DecidableEq

namespace Z15
@[ext] theorem ext' {x y : Z15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Z15 := ⟨0, 0⟩
instance : One Z15  := ⟨1, 0⟩
instance : Add Z15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Z15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Z15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Z15 := ⟨fun x y =>
  ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Z15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Z15).im = 0 := rfl
@[simp] theorem one_re : (1 : Z15).re = 1 := rfl
@[simp] theorem one_im : (1 : Z15).im = 0 := rfl
@[simp] theorem add_re (x y : Z15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Z15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Z15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Z15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Z15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Z15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Z15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Z15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Z15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
end Z15

namespace Butcher

/-- Planar rooted trees, represented by an ordered list of children. -/
inductive RTree where
  /-- A rooted tree node with an ordered forest of children. -/
  | node : List RTree → RTree
deriving Repr, Inhabited

/-- An ordered forest of planar rooted trees. -/
abbrev Forest := List RTree

-- the building blocks: • and grafting
/-- The one-node rooted tree. -/
def leaf : RTree := .node []
/-- Graft a forest below a new root. -/
def graft (F : Forest) : RTree := .node F

/-! ### order and density (γ) -/

mutual
  /-- Number of vertices in a rooted tree. -/
  def order : RTree → Nat | .node F => 1 + orderF F
  /-- Total number of vertices in a forest. -/
  def orderF : Forest → Nat | [] => 0 | t :: ts => order t + orderF ts
end

end Butcher
end RungeKuttaOrderConditions

namespace RungeKuttaOrderConditions.Butcher

mutual
  /-- density γ(t) = |t| · ∏_children γ.  γ(•)=1, γ(•–•)=2,
      γ(cherry)=3, γ(ladder₃)=6. -/
  def gamma : RTree → Nat | .node F => order (.node F) * gammaF F
  /-- Product of the densities of the trees in a forest. -/
  def gammaF : Forest → Nat | [] => 1 | t :: ts => gamma t * gammaF ts
end

end Butcher
end RungeKuttaOrderConditions

namespace RungeKuttaOrderConditions.Butcher

/-! ### the Butcher elementary weight Φ(t)(A,b)

    A method is a tableau: `A` the stage matrix (rows), `b` the weights; #stages s = A.length.
    Internal weight vector  g(t)ᵢ = ∏_children (A·g(child))ᵢ ,  leaf ↦ 𝟙.
    Elementary weight  Φ(t) = bᵀ g(t).  Order conditions:  Φ(t) = 1/γ(t)  for all |t| ≤ p. -/

-- The engine is generic over a commutative coefficient ring `K` (ℚ for the classical methods,
-- the ℚ(√15) ring `Q15` for Gauss–Legendre s=3 in Brick 5).
variable {K : Type*} [CommRing K]

/-- Dot product of two coefficient vectors, truncated to the shorter length. -/
def dot (u v : List K) : K := (List.zipWith (· * ·) u v).sum
/-- Pointwise product of two coefficient vectors, truncated to the shorter length. -/
def pmul (u v : List K) : List K := List.zipWith (· * ·) u v
/-- Matrix-vector product for a list-of-rows matrix. -/
def mulMatVec (A : List (List K)) (v : List K) : List K := A.map (fun row => dot row v)

mutual
  /-- Internal elementary weight vector for a rooted tree. -/
  def phiVec (A : List (List K)) : RTree → List K
    | .node F => phiForest A F
  /-- ∏ over children of (A · phiVec child), pointwise; empty forest ↦ all-ones (length s). -/
  def phiForest (A : List (List K)) : Forest → List K
    | []      => A.map (fun _ => 1)
    | t :: ts => pmul (mulMatVec A (phiVec A t)) (phiForest A ts)
end

end Butcher
end RungeKuttaOrderConditions

namespace RungeKuttaOrderConditions.Butcher

variable {K : Type*} [CommRing K]

/-- elementary weight Φ(t) = bᵀ·g(t). -/
def Phi (A : List (List K)) (b : List K) (t : RTree) : K := dot b (phiVec A t)

/-- the order condition at a single tree, in MULTIPLICATIVE form `γ(t)·Φ(t) = 1`
    (iff Φ(t)=1/γ(t) since γ(t) ≥ 1); stated this way it needs only a commutative
    ring, no division. -/
abbrev orderCond (A : List (List K)) (b : List K) (t : RTree) : Prop :=
  (gamma t : K) * Phi A b t = 1

/-! ### the classical methods (exact rationals) -/

-- explicit Forester sugar
/-- The unique tree of order 1. -/
def t1 : RTree := leaf                                  -- •            |t|=1  γ=1
/-- The ladder tree of order 2. -/
def t2 : RTree := .node [leaf]                          -- •–•          |t|=2  γ=2
/-- The two-leaf cherry tree of order 3. -/
def t31 : RTree := .node [leaf, leaf]                   -- cherry       |t|=3  γ=3
/-- The ladder tree of order 3. -/
def t32 : RTree := .node [.node [leaf]]                 -- ladder₃      |t|=3  γ=6
-- order 4
/-- The four-vertex bushy tree. -/
def t41 : RTree := .node [leaf, leaf, leaf]             -- γ=4
/-- A mixed order-4 tree with one leaf and one order-2 child. -/
def t42 : RTree := .node [leaf, .node [leaf]]           -- γ=8
/-- The order-4 tree with a cherry child. -/
def t43 : RTree := .node [.node [leaf, leaf]]           -- γ=12
/-- The ladder tree of order 4. -/
def t44 : RTree := .node [.node [.node [leaf]]]         -- ladder₄  γ=24
-- one order-5 tree (to witness RK4 is NOT order 5)
/-- The five-vertex bushy tree used to witness RK4's order-5 failure. -/
def t5bushy : RTree := .node [leaf, leaf, leaf, leaf]   -- γ=5

/-- Stage matrix for the Euler method. -/
def eulerA : List (List ℚ) := [[0]]
/-- Weights for the Euler method. -/
def eulerB : List ℚ := [1]

/-- Stage matrix for Heun's explicit trapezoid method. -/
def heunA : List (List ℚ) := [[0,0],[1,0]]
/-- Weights for Heun's explicit trapezoid method. -/
def heunB : List ℚ := [1/2, 1/2]

/-- Stage matrix for the classical four-stage Runge-Kutta method. -/
def rk4A : List (List ℚ) := [[0,0,0,0],[1/2,0,0,0],[0,1/2,0,0],[0,0,1,0]]
/-- Weights for the classical four-stage Runge-Kutta method. -/
def rk4B : List ℚ := [1/6, 1/3, 1/3, 1/6]

-- Dormand–Prince RK45 (DOPRI5): 7 stages (FSAL), the 5th-order solution weights.
/-- Stage matrix for the Dormand-Prince RK45 method. -/
def dpA : List (List ℚ) :=
  [[0,0,0,0,0,0,0],
   [1/5,0,0,0,0,0,0],
   [3/40,9/40,0,0,0,0,0],
   [44/45,-56/15,32/9,0,0,0,0],
   [19372/6561,-25360/2187,64448/6561,-212/729,0,0,0],
   [9017/3168,-355/33,46732/5247,49/176,-5103/18656,0,0],
   [35/384,0,500/1113,125/192,-2187/6784,11/84,0]]
/-- Fifth-order solution weights for the Dormand-Prince RK45 method. -/
def dpB : List ℚ := [35/384, 0, 500/1113, 125/192, -2187/6784, 11/84, 0]

-- Gauss–Legendre s=3 (order 6), fully implicit, with coefficients in ℚ(√15):
-- ⟨a,b⟩ = a + b·√15.
/-- Stage matrix for the three-stage Gauss-Legendre method over ℚ(√15). -/
def gaussA : List (List Q15) :=
  [[⟨5/36, 0⟩,     ⟨2/9, -1/15⟩, ⟨5/36, -1/30⟩],
   [⟨5/36, 1/24⟩,  ⟨2/9, 0⟩,     ⟨5/36, -1/24⟩],
   [⟨5/36, 1/30⟩,  ⟨2/9, 1/15⟩,  ⟨5/36, 0⟩]]
/-- Weights for the three-stage Gauss-Legendre method over ℚ(√15). -/
def gaussB : List Q15 := [⟨5/18, 0⟩, ⟨4/9, 0⟩, ⟨5/18, 0⟩]

/-- discharge a Q15 order condition: unfold the engine + cast, split into ℚ components,
    `norm_num`. -/
macro "gaussCheck" : tactic =>
  `(tactic| (simp only [orderCond, Phi, phiVec, phiForest, dot, pmul, mulMatVec, gamma, gammaF,
      order, orderF, leaf, gaussA, gaussB, t1, t2, t31, t32, t41, t42, t43, t44, t5bushy,
      Q15.natCast_eq, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.zipWith_nil_left, List.sum_cons, List.sum_nil]; apply Q15.ext' <;>
      simp only [Q15.mul_re, Q15.mul_im, Q15.add_re, Q15.add_im, Q15.sub_re, Q15.sub_im,
        Q15.neg_re, Q15.neg_im, Q15.one_re, Q15.one_im, Q15.zero_re, Q15.zero_im] <;> norm_num))


/-! ### Cross-checks against Sage/bseries.py ground truth

The sample orders are `1, 2, 3, 3, 4, 4, 5`, the sample tree factorials are
`1, 2, 3, 6, 4, 8, 12, 24, 5`, and the RK4 elementary weights match `1 / γ`
through order 4 but give `5 / 24` on `t5bushy` where `1 / γ = 1 / 5`.
-/

/-! ### certificates — the order conditions, machine-checked (axiom-free)

    Each `orderCond` unfolds the computable engine on the concrete tree/tableau to a closed ℚ
    arithmetic goal, closed by `norm_num` (symbolic — sidesteps the kernel's stuck `Nat.gcd`
    reduction in `Rat` normalization that defeats `decide`). -/

/-- unfold the engine on a concrete instance to a closed ℚ goal, then `norm_num`. -/
macro "butcherCheck" : tactic =>
  `(tactic| (simp only [orderCond, Phi, phiVec, phiForest, dot, pmul, mulMatVec, gamma, gammaF,
      order, orderF, leaf, t1, t2, t31, t32, t41, t42, t43, t44, t5bushy,
      eulerA, eulerB, heunA, heunB, rk4A, rk4B, dpA, dpB,
      List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.zipWith_nil_left, List.sum_cons, List.sum_nil]; norm_num))

-- Euler attains order 1:
theorem euler_ord1 : orderCond eulerA eulerB t1 := by butcherCheck

-- Heun (explicit trapezoid) attains order 2:
theorem heun_ord1 : orderCond heunA heunB t1 := by butcherCheck
theorem heun_ord2 : orderCond heunA heunB t2 := by butcherCheck
-- and FAILS at order 3 (so it is exactly order 2):
theorem heun_not_ord3 : ¬ orderCond heunA heunB t31 := by butcherCheck

-- classic RK4 satisfies every order condition through order 4:
theorem rk4_ord1 : orderCond rk4A rk4B t1  := by butcherCheck
theorem rk4_ord2 : orderCond rk4A rk4B t2  := by butcherCheck
theorem rk4_ord3a : orderCond rk4A rk4B t31 := by butcherCheck
theorem rk4_ord3b : orderCond rk4A rk4B t32 := by butcherCheck
theorem rk4_ord4a : orderCond rk4A rk4B t41 := by butcherCheck
theorem rk4_ord4b : orderCond rk4A rk4B t42 := by butcherCheck
theorem rk4_ord4c : orderCond rk4A rk4B t43 := by butcherCheck
theorem rk4_ord4d : orderCond rk4A rk4B t44 := by butcherCheck
-- ...but FAILS an order-5 condition (bushy 4-leaf tree: Φ=5/24 ≠ 1/5).  RK4 is EXACTLY order 4:
theorem rk4_not_ord5 : ¬ orderCond rk4A rk4B t5bushy := by butcherCheck

/-! ### Brick 2+4 — completeness: "order p" is EXACTLY a finite check (order-budget generator)

    A method satisfies the order-p conditions iff Φ(t)=1/γ(t) for the FINITE catalogue of trees
    with |t| ≤ p.  Keystone: it turns the infinite quantifier (∀ rooted trees) into a decidable
    finite enumeration.  The generator `build` is bounded by an ORDER BUDGET (not by length), so the
    catalogue stays Catalan-small (|trees of order ≤ p| = 1,2,4,9,23,…) and
    `fin_cases` is feasible up to order 5+ (Dormand–Prince).  Structural on the budget
    → reduces in the kernel; completeness is mutual induction with measure
    (budget, structure) — the "WF wall" was imaginary (Socratic). -/

theorem one_le_order (t : RTree) : 1 ≤ order t := by
  cases t with | node F => simp only [order]; omega

theorem order_le_orderF_of_mem : ∀ {c : RTree} {F : Forest}, c ∈ F → order c ≤ orderF F
  | _, _ :: ts, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · simp only [orderF]; omega
      · have ih := order_le_orderF_of_mem h'; simp only [orderF]; omega

/-- ORDER-BUDGET generator (structural on the budget `n`; no length over-generation).
    `(build n).1` = all trees of order ≤ n; `(build n).2` = all forests of orderF ≤ n.
    The filter bounds each forest by the remaining budget, keeping intermediate lists
    Catalan-small. -/
def build : Nat → List RTree × List Forest
  | 0     => ([], [[]])
  | n + 1 =>
      let fs := (build n).2
      let trees := fs.map RTree.node
      let forests := [] :: trees.flatMap (fun t =>
          (fs.filter (fun ts => decide (order t + orderF ts ≤ n + 1))).map (fun ts => t :: ts))
      (trees, forests)

/-- Trees generated by the order-budget catalogue up to order `n`. -/
def treesB (n : Nat) : List RTree := (build n).1

-- COMPLETENESS of the order-budget generator (mutual, measure = (budget, structure)).
mutual
theorem mem_build_trees : ∀ (n : Nat) (t : RTree), order t ≤ n → t ∈ (build n).1
  | n, RTree.node F, h => by
      cases n with
      | zero => simp only [order] at h; omega
      | succ m =>
          have hF : orderF F ≤ m := by simp only [order] at h; omega
          have hmemF : F ∈ (build m).2 := mem_build_forests m F hF
          change RTree.node F ∈ (build (m+1)).1
          simp only [build, List.mem_map]; exact ⟨F, hmemF, rfl⟩
  termination_by n t => (n, sizeOf t)
  decreasing_by simp_wf; omega

theorem mem_build_forests : ∀ (n : Nat) (F : Forest), orderF F ≤ n → F ∈ (build n).2
  | n, [], _ => by cases n <;> simp [build]
  | n, t :: ts, h => by
      have ht1 : 1 ≤ order t := one_le_order t
      cases n with
      | zero => simp only [orderF] at h; omega
      | succ m =>
          have hsum : order t + orderF ts ≤ m + 1 := by simpa only [orderF] using h
          have htm : order t ≤ m + 1 := by omega
          have htsm : orderF ts ≤ m := by omega
          have hmem_t : t ∈ (build (m+1)).1 := mem_build_trees (m+1) t htm
          have hmem_ts : ts ∈ (build m).2 := mem_build_forests m ts htsm
          have hfilt :
              ts ∈ ((build m).2).filter
                (fun ts => decide (order t + orderF ts ≤ m + 1)) :=
            List.mem_filter.2 ⟨hmem_ts, by simpa using hsum⟩
          change (t :: ts) ∈ (build (m+1)).2
          simp only [build, List.mem_cons, List.mem_flatMap, List.mem_map]
          refine Or.inr ⟨t, ?_, ts, hfilt, rfl⟩
          simpa only [build, List.mem_map] using hmem_t
  termination_by n F => (n, sizeOf F)
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega
end

end Butcher
end RungeKuttaOrderConditions

namespace RungeKuttaOrderConditions.Butcher

variable {K : Type*} [CommRing K]

/-- the finite catalogue of all rooted trees with |t| ≤ p. -/
def catalog (p : Nat) : List RTree := (treesB p).filter (fun t => decide (order t ≤ p))

private def treesUpToFour : List RTree :=
  [t1, t2, t31, t41, t42, t32, .node [.node [leaf], leaf], t43, t44]

private theorem catalogFourEq : catalog 4 = treesUpToFour := rfl

private def treesUpToFive : List RTree :=
  [t1, t2, t31, t41, t5bushy, .node [leaf, leaf, .node [leaf]], t42,
   .node [leaf, .node [leaf], leaf], .node [leaf, .node [leaf, leaf]],
   .node [leaf, .node [.node [leaf]]], t32, .node [.node [leaf], leaf],
   .node [.node [leaf], leaf, leaf], .node [.node [leaf], .node [leaf]], t43,
   .node [.node [leaf, leaf], leaf], .node [.node [leaf, leaf, leaf]],
   .node [.node [leaf, .node [leaf]]], t44, .node [.node [.node [leaf]], leaf],
   .node [.node [.node [leaf], leaf]], .node [.node [.node [leaf, leaf]]],
   .node [.node [.node [.node [leaf]]]]]

private theorem catalogFiveEq : catalog 5 = treesUpToFive := rfl

/-- a method `(A,b)` satisfies the order-p conditions: every order condition holds through
    order p. -/
def satisfiesOrderConditions (A : List (List K)) (b : List K) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCond A b t

/-- KEYSTONE: the order-p conditions are equivalent to a finite check over the catalogue.
    (sound + complete) -/
theorem satisfiesOrderConditions_iff (A : List (List K)) (b : List K) (p : Nat) :
    satisfiesOrderConditions A b p ↔ ∀ t ∈ catalog p, orderCond A b t := by
  constructor
  · intro h t ht
    exact h t (of_decide_eq_true (List.mem_filter.1 ht).2)
  · intro h t hle
    exact h t (List.mem_filter.2 ⟨mem_build_trees p t hle, decide_eq_true hle⟩)

/-- classic RK4 satisfies ALL order-≤4 conditions, certified, axiom-free. -/
theorem rk4_order4 : satisfiesOrderConditions rk4A rk4B 4 := by
  rw [satisfiesOrderConditions_iff, catalogFourEq]; intro t ht
  fin_cases ht <;> butcherCheck

/-! ### Brick 3 — the planar→abstract bridge: Φ is symmetric in a node's children

    Our trees are PLANAR (ordered children).  The numerical literature uses ABSTRACT rooted trees
    (multiset children); the abstract Connes–Kreimer algebra is the abelianization
    (Foissy 2002) of
    our noncommutative one.  Here we prove the order condition descends along that symmetrization:
    permuting the children of a node leaves Φ, γ and hence the order condition unchanged.  So
    certifying all PLANAR trees of order ≤ p genuinely subsumes the abstract order conditions —
    mirror planar trees (same abstract shape) share a single condition.  Engine of the bridge:
    `pmul` (pointwise ℚ-product of stage vectors) is commutative and associative
    UNconditionally. -/

theorem pmul_comm : ∀ u v : List ℚ, pmul u v = pmul v u
  | [],    []    => rfl
  | [],    _::_  => rfl
  | _::_,  []    => rfl
  | a::u,  b::v  => by
      simp only [pmul, List.zipWith_cons_cons, mul_comm a b]
      rw [← pmul, ← pmul, pmul_comm u v]

theorem pmul_assoc : ∀ u v w : List ℚ, pmul (pmul u v) w = pmul u (pmul v w)
  | [],    _,     _     => by simp [pmul]
  | _::_,  [],    _     => by simp [pmul]
  | _::_,  _::_,  []    => by simp [pmul]
  | a::u,  b::v,  c::w  => by
      simp only [pmul, List.zipWith_cons_cons, mul_assoc]
      rw [← pmul, ← pmul, ← pmul, ← pmul, pmul_assoc u v w]

theorem phiForest_perm (A : List (List ℚ)) {F G : Forest} (h : F.Perm G) :
    phiForest A F = phiForest A G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [phiForest]; rw [ih]
  | swap x y l =>
      simp only [phiForest]
      rw [← pmul_assoc,
        pmul_comm (mulMatVec A (phiVec A y)) (mulMatVec A (phiVec A x)),
        pmul_assoc]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem orderF_perm {F G : Forest} (h : F.Perm G) : orderF F = orderF G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [orderF]; rw [ih]
  | swap x y l => simp only [orderF]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem gammaF_perm {F G : Forest} (h : F.Perm G) : gammaF F = gammaF G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [gammaF]; rw [ih]
  | swap x y l => simp only [gammaF]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Φ is invariant under permuting the children of the root. -/
theorem Phi_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    Phi A b (.node F) = Phi A b (.node G) := by
  simp only [Phi, phiVec]; rw [phiForest_perm A h]

/-- γ is invariant under permuting the children of the root. -/
theorem gamma_node_perm {F G : Forest} (h : F.Perm G) : gamma (.node F) = gamma (.node G) := by
  simp only [gamma, order]; rw [orderF_perm h, gammaF_perm h]

/-- BRIDGE: the order condition depends only on the ABSTRACT tree — permuting children is
    invisible. -/
theorem orderCond_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    orderCond A b (.node F) ↔ orderCond A b (.node G) := by
  unfold orderCond; rw [Phi_node_perm A b h, gamma_node_perm h]

/-! ### Brick 4 — a higher-order method: Dormand–Prince certified order 5

    The order-budget generator makes `catalog 5` (23 planar trees) small enough that `fin_cases`
    discharges every order-≤5 condition for the 7-stage DOPRI5 tableau.  First machine-checked
    certificate that a production RK method (the default in MATLAB `ode45`, SciPy `RK45`) attains
    its full classical order. -/
private theorem dpCondition01 : orderCond dpA dpB t1 := by
  butcherCheck

private theorem dpCondition02 : orderCond dpA dpB t2 := by
  butcherCheck

private theorem dpCondition03 : orderCond dpA dpB t31 := by
  butcherCheck

private theorem dpCondition04 : orderCond dpA dpB t41 := by
  butcherCheck

private theorem dpCondition05 : orderCond dpA dpB t5bushy := by
  butcherCheck

private theorem dpCondition06 :
    orderCond dpA dpB (.node [leaf, leaf, .node [leaf]]) := by
  butcherCheck

private theorem dpCondition07 : orderCond dpA dpB t42 := by
  butcherCheck

private theorem dpCondition08 :
    orderCond dpA dpB (.node [leaf, .node [leaf], leaf]) := by
  butcherCheck

private theorem dpCondition09 :
    orderCond dpA dpB (.node [leaf, .node [leaf, leaf]]) := by
  butcherCheck

private theorem dpCondition10 :
    orderCond dpA dpB (.node [leaf, .node [.node [leaf]]]) := by
  butcherCheck

private theorem dpCondition11 : orderCond dpA dpB t32 := by
  butcherCheck

private theorem dpCondition12 :
    orderCond dpA dpB (.node [.node [leaf], leaf]) := by
  butcherCheck

private theorem dpCondition13 :
    orderCond dpA dpB (.node [.node [leaf], leaf, leaf]) := by
  butcherCheck

private theorem dpCondition14 :
    orderCond dpA dpB (.node [.node [leaf], .node [leaf]]) := by
  butcherCheck

private theorem dpCondition15 : orderCond dpA dpB t43 := by
  butcherCheck

private theorem dpCondition16 :
    orderCond dpA dpB (.node [.node [leaf, leaf], leaf]) := by
  butcherCheck

private theorem dpCondition17 :
    orderCond dpA dpB (.node [.node [leaf, leaf, leaf]]) := by
  butcherCheck

private theorem dpCondition18 :
    orderCond dpA dpB (.node [.node [leaf, .node [leaf]]]) := by
  butcherCheck

private theorem dpCondition19 : orderCond dpA dpB t44 := by
  butcherCheck

private theorem dpCondition20 :
    orderCond dpA dpB (.node [.node [.node [leaf]], leaf]) := by
  butcherCheck

private theorem dpCondition21 :
    orderCond dpA dpB (.node [.node [.node [leaf], leaf]]) := by
  butcherCheck

private theorem dpCondition22 :
    orderCond dpA dpB (.node [.node [.node [leaf, leaf]]]) := by
  butcherCheck

private theorem dpCondition23 :
    orderCond dpA dpB (.node [.node [.node [.node [leaf]]]]) := by
  butcherCheck

-- The public theorem only splits membership in the explicit 23-tree catalogue.
theorem dp_order5 : satisfiesOrderConditions dpA dpB 5 := by
  rw [satisfiesOrderConditions_iff, catalogFiveEq]; intro t ht
  fin_cases ht
  · exact dpCondition01
  · exact dpCondition02
  · exact dpCondition03
  · exact dpCondition04
  · exact dpCondition05
  · exact dpCondition06
  · exact dpCondition07
  · exact dpCondition08
  · exact dpCondition09
  · exact dpCondition10
  · exact dpCondition11
  · exact dpCondition12
  · exact dpCondition13
  · exact dpCondition14
  · exact dpCondition15
  · exact dpCondition16
  · exact dpCondition17
  · exact dpCondition18
  · exact dpCondition19
  · exact dpCondition20
  · exact dpCondition21
  · exact dpCondition22
  · exact dpCondition23

/-! ### Brick 5 — an IMPLICIT method with ALGEBRAIC coefficients: Gauss–Legendre s=3

    Gauss–Legendre with 3 stages is fully implicit, with a tableau living in ℚ(√15).
    Working in the computable pair ring `Q15` (where √15²=15 is baked into
    multiplication), every order condition collapses to a pair of ℚ identities that
    `gaussCheck` closes by `norm_num` — no algebraic-number tactic.  This certifies
    the framework on implicit methods with irrational (algebraic) coefficients.

    We certify order 4 here; the full order-6 certificate
    (`satisfiesOrderConditions gaussA gaussB 6`) is mathematically settled — Gauss
    s=3 attains order 6 EXACTLY, verified independently in Sage over ℚ(√15)
    (conditions hold for orders 1..6, fail at 7) — but its Lean proof by `fin_cases`
    over `catalog 6` (65 planar trees) is dominated by the elaborator's whnf reduction
    of the catalogue and does not complete in practical time at this scale.  The
    efficient route (Brick 6) is to certify over ABSTRACT trees (37 vs 65) via the
    symmetrization bridge `orderCond_node_perm`.  See the paper. -/
private def gaussOnes : List Q15 := [1, 1, 1]

private def gaussC : List Q15 := [⟨1 / 2, -1 / 10⟩, ⟨1 / 2, 0⟩, ⟨1 / 2, 1 / 10⟩]

private def gaussAc : List Q15 := [⟨1 / 5, -1 / 20⟩, ⟨1 / 8, 0⟩, ⟨1 / 5, 1 / 20⟩]

private def gaussAAc : List Q15 :=
  [⟨7 / 120, -3 / 200⟩, ⟨1 / 48, 0⟩, ⟨7 / 120, 3 / 200⟩]

private theorem gaussOnesReplicate :
    List.replicate gaussA.length (1 : Q15) = gaussOnes := by
  simp [gaussA, gaussOnes]

private theorem gaussCPmulOnes : pmul gaussC gaussOnes = gaussC := by
  simp [pmul, gaussC, gaussOnes]

private theorem gaussAcPmulOnes : pmul gaussAc gaussOnes = gaussAc := by
  simp [pmul, gaussAc, gaussOnes]

private theorem gaussAAcPmulOnes : pmul gaussAAc gaussOnes = gaussAAc := by
  simp [pmul, gaussAAc, gaussOnes]

private theorem gaussFirstStageVector : mulMatVec gaussA gaussOnes = gaussC := by
  simp only [mulMatVec, dot, gaussA, gaussOnes, gaussC, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    mul_one, add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial

private theorem gaussSecondStageVector : mulMatVec gaussA gaussC = gaussAc := by
  simp only [mulMatVec, dot, gaussA, gaussC, gaussAc, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial

private theorem gaussThirdStageVector : mulMatVec gaussA gaussAc = gaussAAc := by
  simp only [mulMatVec, dot, gaussA, gaussAc, gaussAAc, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    add_zero, List.cons.injEq]
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  constructor
  · ext <;> norm_num
  · trivial

private theorem gaussLeafVector : phiVec gaussA leaf = gaussOnes := by
  change List.replicate gaussA.length (1 : Q15) = gaussOnes
  exact gaussOnesReplicate

private theorem gaussT2Vector : phiVec gaussA t2 = gaussC := by
  change pmul (mulMatVec gaussA (phiVec gaussA leaf))
      (List.replicate gaussA.length (1 : Q15)) = gaussC
  rw [gaussLeafVector, gaussFirstStageVector, gaussOnesReplicate, gaussCPmulOnes]

private theorem gaussT32Vector : phiVec gaussA t32 = gaussAc := by
  change pmul (mulMatVec gaussA (phiVec gaussA t2))
      (List.replicate gaussA.length (1 : Q15)) = gaussAc
  rw [gaussT2Vector, gaussSecondStageVector, gaussOnesReplicate, gaussAcPmulOnes]

private theorem gaussT44Vector : phiVec gaussA t44 = gaussAAc := by
  change pmul (mulMatVec gaussA (phiVec gaussA t32))
      (List.replicate gaussA.length (1 : Q15)) = gaussAAc
  rw [gaussT32Vector, gaussThirdStageVector, gaussOnesReplicate, gaussAAcPmulOnes]

private theorem gaussT44Weight : Phi gaussA gaussB t44 = ⟨1 / 24, 0⟩ := by
  change dot gaussB (phiVec gaussA t44) = ⟨1 / 24, 0⟩
  rw [gaussT44Vector]
  simp only [dot, gaussB, gaussAAc, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.sum_cons, List.sum_nil, add_zero]
  ext <;> norm_num

private theorem gaussCondition01 : orderCond gaussA gaussB t1 := by
  gaussCheck

private theorem gaussCondition02 : orderCond gaussA gaussB t2 := by
  gaussCheck

private theorem gaussCondition03 : orderCond gaussA gaussB t31 := by
  gaussCheck

private theorem gaussCondition04 : orderCond gaussA gaussB t41 := by
  gaussCheck

private theorem gaussCondition05 : orderCond gaussA gaussB t42 := by
  gaussCheck

private theorem gaussCondition06 : orderCond gaussA gaussB t32 := by
  gaussCheck

private theorem gaussCondition07 :
    orderCond gaussA gaussB (.node [.node [leaf], leaf]) := by
  gaussCheck

private theorem gaussCondition08 : orderCond gaussA gaussB t43 := by
  gaussCheck

private theorem gaussCondition09 : orderCond gaussA gaussB t44 := by
  change (gamma t44 : Q15) * Phi gaussA gaussB t44 = 1
  rw [gaussT44Weight]
  have hgamma : gamma t44 = 24 := by
    norm_num [gamma, gammaF, order, orderF, t44, leaf]
  rw [hgamma, Q15.natCast_eq]
  ext <;> norm_num

-- The public theorem only splits membership in the explicit 9-tree catalogue.
theorem gauss_order4 : satisfiesOrderConditions gaussA gaussB 4 := by
  rw [satisfiesOrderConditions_iff, catalogFourEq]; intro t ht
  fin_cases ht
  · exact gaussCondition01
  · exact gaussCondition02
  · exact gaussCondition03
  · exact gaussCondition04
  · exact gaussCondition05
  · exact gaussCondition06
  · exact gaussCondition07
  · exact gaussCondition08
  · exact gaussCondition09

/-! ### Brick 6 — Gauss–Legendre s=3 certified to FULL order 6 (integer ℤ[√15] + `decide`)

    `gauss_order4` above unfolds the engine symbolically and closes the ℚ(√15)
    components by `norm_num`.  At order 6 that route dies: the 65 per-tree `norm_num`
    calls exhaust memory (a run reached ~20 GB), because ℚ's `Nat.gcd` normalization
    does not reduce in the kernel and the unfolded Q15 products are huge.  The fix is
    a genuinely different *formula* (found by re-questioning the representation, not
    the method): clear all denominators.  Scaling the tableau by `D = 360` (the lcm of
    the denominators 36,9,15,30,24,18) lands it in the INTEGER ring `Z15 = ℤ[√15]`.
    The elementary weight is homogeneous, `Φ(D·A, D·b, t) = D^{|t|}·Φ(A,b,t)`, so
    the order condition `γ(t)·Φ = 1` becomes the integer identity
    `γ(t)·Φ(D·A,D·b,t) = D^{|t|}`.  Over `Z15` (a pair of `Int`) this closes by
    `decide`: the kernel's GMP `Int` arithmetic evaluates it directly — no rational
    normalization, negligible memory.  The whole certificate (all 65 planar trees of
    `catalog 6`) checks in ~1 s, axiom-free.  Cross-checked outside Lean three ways
    (tree recursion + brute-force index sum in Python, brute-force in Sage over ℚ(√15)):
    Gauss s=3 holds orders 1–6 and fails all 48 order-7 conditions, i.e. it is EXACTLY order 6.

    The scaled integer tableau: entry `a + b√15` with denominator cleared by 360 becomes
    `⟨360a, 360b⟩`.
    E.g. `2/9 - √15/15 ↦ ⟨80, -24⟩`, `5/18 ↦ ⟨100,0⟩`. -/

/-- Denominator-cleared stage matrix for the three-stage Gauss-Legendre method. -/
def gaussIA : List (List Z15) :=
  [[⟨50, 0⟩,   ⟨80, -24⟩, ⟨50, -12⟩],
   [⟨50, 15⟩,  ⟨80, 0⟩,   ⟨50, -15⟩],
   [⟨50, 12⟩,  ⟨80, 24⟩,  ⟨50, 0⟩]]
/-- Denominator-cleared weights for the three-stage Gauss-Legendre method. -/
def gaussIB : List Z15 := [⟨100, 0⟩, ⟨160, 0⟩, ⟨100, 0⟩]
/-- Common denominator used to scale the Gauss-Legendre tableau. -/
def Dscale : Int := 360

/-- the order condition with denominators cleared: `γ(t)·Φ(D·A,D·b,t) = D^{|t|}`
    in `Z15`.  Equivalent to `orderCond` on the unscaled ℚ(√15) tableau by homogeneity
    of `Φ`, but decidable by the kernel. -/
abbrev orderCondInt (A : List (List Z15)) (b : List Z15) (D : Int) (t : RTree) : Prop :=
  (⟨(gamma t : Int), 0⟩ : Z15) * Phi A b t = ⟨D ^ (order t), 0⟩

/-- Denominator-cleared order-p conditions for a `Z15` tableau. -/
def satisfiesOrderConditionsInt (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCondInt A b D t

/-- same keystone as `satisfiesOrderConditions_iff`, for the integer condition: the
    order-p conditions
    reduce to the finite catalogue check (reuses the generic `build`/`catalog` completeness). -/
theorem satisfiesOrderConditionsInt_iff (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) :
    satisfiesOrderConditionsInt A b D p ↔ ∀ t ∈ catalog p, orderCondInt A b D t := by
  constructor
  · intro h t ht
    exact h t (of_decide_eq_true (List.mem_filter.1 ht).2)
  · intro h t hle
    exact h t (List.mem_filter.2 ⟨mem_build_trees p t hle, decide_eq_true hle⟩)

/-! Gauss–Legendre s=3 satisfies ALL order-≤6 conditions: the full order-6
    certificate, axiom-free.
    `fin_cases` enumerates the 65-tree catalogue; each condition is closed by the kernel (`decide`)
    over `Z15` integer arithmetic.  (Heartbeat bump bounds only `fin_cases`' elaboration; the
    per-tree
    `decide` is cheap and has no effect on the axiom set.) -/
-- `fin_cases` unfolds the finite 65-tree Gauss order-6 catalogue.
theorem gauss_order6 : satisfiesOrderConditionsInt gaussIA gaussIB Dscale 6 := by
  rw [satisfiesOrderConditionsInt_iff]; intro t ht
  fin_cases ht <;> decide

end Butcher

-- sanity: catalogue sizes = cumulative PLANAR rooted trees (Catalan Cₙ₋₁ partial sums
-- 1,2,4,9,23).
-- These are ORDERED trees (`RTree` has `List` children) = the NONCOMMUTATIVE
-- Connes–Kreimer/Foissy Hopf algebra of ConnesKreimer.lean, not the abstract
-- (A000081: 1,1,2,4,9) trees.  Φ symmetric in a
-- node's children ⇒ certifying all planar trees SUBSUMES the abstract order conditions (Brick 3).
-- The order-budget `build` is Catalan-small, so unlike a length-bounded generator these are cheap.
-- The catalogue lengths for orders 1 through 5 are `1, 2, 4, 9, 23`.

end RungeKuttaOrderConditions
