/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.GraphicMatroid

/-!
  A finite formalization of the finite part of the hard-sphere NBC
  proof.  `points` is a finite configuration ledger, `trees` is a finite list
  of candidate spanning trees, and `region t x` is the NBC ownership test.

  The central theorem is a literal finite Tonelli/double-counting proof:

      sum_x weight(x) * NBCMultiplicity(x)
        = sum_t NBCRegionWeight(t).

  No measure theorem, graph theorem, or opaque assumption is imported here.  The
  continuous hard-sphere interpretation is obtained by replacing the finite
  weight sum with Lebesgue integration after this algebraic identity.
-/

namespace HsVirial



/-- The recursive sum of a finite list of natural numbers. -/
def sumNat : List Nat -> Nat
  | [] => 0
  | a :: as => a + sumNat as

theorem sumNat_replicate_zero (n : Nat) :
    sumNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate, sumNat, ih]

theorem sumNat_append {as bs : List Nat} :
    sumNat (as ++ bs) = sumNat as + sumNat bs := by
  induction as with
  | nil => simp [sumNat]
  | cons a as ih =>
      simp [sumNat, ih, Nat.add_assoc]

theorem sumNat_map_congr {X : Type} {xs : List X} {f g : X -> Nat}
    (h : forall x, f x = g x) :
    sumNat (xs.map f) = sumNat (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [sumNat, h, ih]

theorem list_map_map {X Y Z : Type} (xs : List X) (f : X -> Y)
    (g : Y -> Z) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ih]

theorem sumNat_map_add {X : Type} (xs : List X) (f g : X -> Nat) :
    sumNat (xs.map (fun x => f x + g x)) =
      sumNat (xs.map f) + sumNat (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
       simp [sumNat, ih, Nat.add_assoc, Nat.add_left_comm]

theorem sumNat_map_zero {X : Type} (xs : List X) :
    sumNat (xs.map (fun _ => 0)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [sumNat, sumNat_replicate_zero]

theorem mul_sumNat {xs : List Nat} (a : Nat) :
    a * sumNat xs = sumNat (xs.map (fun b => a * b)) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp [sumNat, ih, Nat.mul_add]

theorem sumNat_swap {X Y : Type} (xs : List X) (ys : List Y)
    (f : X -> Y -> Nat) :
    sumNat (xs.map (fun x => sumNat (ys.map (f x)))) =
      sumNat (ys.map (fun y => sumNat (xs.map (fun x => f x y)))) := by
  induction xs with
  | nil =>
      simp [sumNat, sumNat_replicate_zero]
  | cons x xs ih =>
      calc
        sumNat ((x :: xs).map (fun x => sumNat (ys.map (f x)))) =
            sumNat (ys.map (f x)) +
              sumNat (xs.map (fun x => sumNat (ys.map (f x)))) := by
          rfl
        _ = sumNat (ys.map (f x)) +
              sumNat (ys.map (fun y => sumNat (xs.map (fun x => f x y)))) := by
          rw [ih]
        _ = sumNat (ys.map (fun y =>
              f x y + sumNat (xs.map (fun x => f x y)))) := by
          symm
          exact sumNat_map_add ys (fun y => f x y)
            (fun y => sumNat (xs.map (fun x => f x y)))
        _ = sumNat (ys.map (fun y =>
              sumNat ((x :: xs).map (fun x => f x y)))) := by
          apply sumNat_map_congr
          intro y
          rfl

/-- Keep a natural-number weight exactly when the Boolean predicate holds. -/
def indicator (p : Bool) (a : Nat) : Nat :=
  if p then a else 0

/-- Count the listed tree regions containing the point, including repeated tree entries. -/
def nbcMultiplicity {X T : Type} (trees : List T)
    (region : T -> X -> Bool) (x : X) : Nat :=
  sumNat (trees.map (fun t => indicator (region t x) 1))

/-- Sum point weights over one tree region. -/
def nbcRegionWeight {X T : Type} (points : List X) (weight : X -> Nat)
    (region : T -> X -> Bool) (t : T) : Nat :=
  sumNat (points.map (fun x => indicator (region t x) (weight x)))

/-- Sum point weights multiplied by the number of tree regions containing the point. -/
def pointwiseNbcWeight {X T : Type} (points : List X) (trees : List T)
    (weight : X -> Nat) (region : T -> X -> Bool) : Nat :=
  sumNat (points.map (fun x => weight x * nbcMultiplicity trees region x))

/-- Sum the weighted sizes of all listed tree regions. -/
def nbcVolumeSum {X T : Type} (points : List X) (trees : List T)
    (weight : X -> Nat) (region : T -> X -> Bool) : Nat :=
  sumNat (trees.map (nbcRegionWeight points weight region))

theorem indicator_mul_one (p : Bool) (a : Nat) :
    a * indicator p 1 = indicator p a := by
  cases p <;> simp [indicator]

theorem nbc_volume_identity {X T : Type} (points : List X) (trees : List T)
    (weight : X -> Nat) (region : T -> X -> Bool) :
    pointwiseNbcWeight points trees weight region =
      nbcVolumeSum points trees weight region := by
  unfold pointwiseNbcWeight nbcVolumeSum nbcMultiplicity nbcRegionWeight
  calc
    sumNat (points.map (fun x =>
        weight x * sumNat (trees.map (fun t => indicator (region t x) 1)))) =
      sumNat (points.map (fun x =>
        sumNat (trees.map (fun t =>
          weight x * indicator (region t x) 1)))) := by
      apply sumNat_map_congr
      intro x
      calc
        weight x * sumNat (trees.map (fun t =>
            indicator (region t x) 1)) =
            sumNat ((trees.map (fun t => indicator (region t x) 1)).map
              (fun b => weight x * b)) :=
          mul_sumNat (xs := trees.map (fun t => indicator (region t x) 1))
            (weight x)
        _ = sumNat (trees.map (fun t =>
            weight x * indicator (region t x) 1)) := by
          rw [list_map_map]
    _ = sumNat (trees.map (fun t =>
        sumNat (points.map (fun x =>
          weight x * indicator (region t x) 1)))) := by
        exact sumNat_swap points trees
          (fun x t => weight x * indicator (region t x) 1)
    _ = sumNat (trees.map (fun t =>
        sumNat (points.map (fun x =>
          indicator (region t x) (weight x))))) := by
        apply sumNat_map_congr
        intro t
        apply sumNat_map_congr
        intro x
        exact indicator_mul_one (region t x) (weight x)

/- The pointwise expression is the finite counterpart of the integral
   multiplicity.  This name is kept separate so that a later measure-theory
   layer can state its bridge without changing this checked algebra. -/
theorem nbc_multiplicity_is_region_sum {X T : Type}
    (points : List X) (trees : List T) (weight : X -> Nat)
    (region : T -> X -> Bool) :
    sumNat (points.map (fun x =>
      weight x * nbcMultiplicity trees region x)) =
      sumNat (trees.map (nbcRegionWeight points weight region)) := by
  exact nbc_volume_identity points trees weight region

/-- The recursive sum of a finite list of integers. -/
def sumInt : List Int -> Int
  | [] => 0
  | a :: as => a + sumInt as

/-- The alternating integer sign associated with a natural-number size. -/
def paritySign : Nat -> Int
  | 0 => 1
  | n + 1 => -paritySign n

/-!
  This is the finite active-graph restriction used before the NBC step.  The
  list `graphs` represents the complete finite list of edge subsets.  A Mayer
  term is zero unless every edge is active; otherwise its product is the
  parity sign of the number of edges.
-/

/-- Check that every edge in a list is active. -/
def allActive {E : Type} (active : E -> Bool) : List E -> Bool
  | [] => true
  | e :: es => if active e then allActive active es else false

/-- The parity contribution of a connected edge list with every edge active. -/
def signedMayerTerm {E : Type} (connected : List E -> Bool)
    (active : E -> Bool) (edges : List E) : Int :=
  if connected edges then
    if allActive active edges then paritySign edges.length else 0
  else 0

/-- Sum signed Mayer terms over a list of candidate edge sets. -/
def signedMayerSum {E : Type} (graphs : List (List E))
    (connected : List E -> Bool) (active : E -> Bool) : Int :=
  sumInt (graphs.map (signedMayerTerm connected active))

/-- Restrict the graph list to active edge sets before summing connected contributions. -/
def activeGraphSum {E : Type} (graphs : List (List E))
    (connected : List E -> Bool) (active : E -> Bool) : Int :=
  sumInt ((graphs.filter (allActive active)).map (fun edges =>
    if connected edges then paritySign edges.length else 0))

theorem signed_mayer_restriction {E : Type}
    (graphs : List (List E)) (connected : List E -> Bool)
    (active : E -> Bool) :
    signedMayerSum graphs connected active =
      activeGraphSum graphs connected active := by
  induction graphs with
  | nil => rfl
  | cons graph rest ih =>
      cases h : allActive active graph with
      | false =>
          simp only [signedMayerSum, List.map_cons, signedMayerTerm, h, Bool.false_eq_true,
            ↓reduceIte, ite_self, sumInt, zero_add, activeGraphSum, not_false_eq_true,
            List.filter_cons_of_neg]
          exact ih
      | true =>
          simp only [signedMayerSum, List.map_cons, signedMayerTerm, h, ↓reduceIte, sumInt,
            activeGraphSum, List.filter_cons_of_pos, add_right_inj]
          exact ih

/-!
  The next block formalizes the sign-reversing part independently of graph
  representation.  For a fixed ordered graph, `all` is the finite list of
  connected edge sets, `good` is the finite list of NBC trees, and `badPairs`
  is produced by the least broken-circuit toggle described in the TeX proof.
  The theorem checks, in the kernel, that every paired bad contribution
  disappears.
-/

/-- The sum of parity signs for the sizes of a list of objects. -/
def signedList {A : Type} (xs : List A) (size : A -> Nat) : Int :=
  sumInt (xs.map (fun a => paritySign (size a)))

theorem sumInt_append {as bs : List Int} :
    sumInt (as ++ bs) = sumInt as + sumInt bs := by
  induction as with
  | nil => simp [sumInt]
  | cons a as ih =>
      simp [sumInt, ih, Int.add_assoc]

theorem sumInt_map_congr {A : Type} {xs : List A} {f g : A -> Int}
    (h : forall a, f a = g a) :
    sumInt (xs.map f) = sumInt (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp [sumInt, h, ih]

theorem signedList_eq_constant {A : Type} (xs : List A)
    (size : A -> Nat) (rank : Nat)
    (same_sign : forall a, a ∈ xs ->
      paritySign (size a) = paritySign rank) :
    signedList xs size =
      sumInt (xs.map (fun _ => paritySign rank)) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      have ha : paritySign (size a) = paritySign rank :=
        same_sign a (List.mem_cons_self)
      have htail : forall b, b ∈ as ->
          paritySign (size b) = paritySign rank := by
        intro b hb
        exact same_sign b (List.mem_cons_of_mem a hb)
      unfold signedList
      change paritySign (size a) +
          sumInt (as.map (fun b => paritySign (size b))) =
        paritySign rank + sumInt (as.map (fun _ => paritySign rank))
      rw [ha]
      exact congrArg (fun z => paritySign rank + z) (ih htail)

theorem sumInt_perm {as bs : List Int} (h : as.Perm bs) :
    sumInt as = sumInt bs := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp [sumInt, ih]
  | swap a b as =>
       simp [sumInt, Int.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

theorem sumInt_pair_zero {A : Type} (pairs : List (A × A))
    (size : A -> Nat)
    (opposite : forall p : A × A,
      paritySign (size p.1) + paritySign (size p.2) = 0) :
    sumInt (pairs.flatMap (fun p =>
      [paritySign (size p.1), paritySign (size p.2)])) = 0 := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
       simp [sumInt, opposite, ih]

/-- A decomposition into surviving objects and pairs with opposite parity contributions. -/
structure NBCPairing (A : Type) where
  /-- The full list before cancellation. -/
  all : List A
  /-- The surviving list of no-broken-circuit objects. -/
  good : List A
  /-- Pairs whose signed contributions cancel. -/
  badPairs : List (A × A)
  /-- The size determining the parity sign of each object. -/
  size : A -> Nat
  /-- The common size of the surviving objects. -/
  rank : Nat
  decomposition :
    all = good ++ badPairs.flatMap (fun p => [p.1, p.2])
  opposite : forall p : A × A,
    paritySign (size p.1) + paritySign (size p.2) = 0
  goodParity : forall a, a ∈ good ->
    paritySign (size a) = paritySign rank

theorem signed_sum_of_nbc_pairing {A : Type} (P : NBCPairing A) :
    signedList P.all P.size = signedList P.good P.size := by
  unfold signedList
  rw [P.decomposition]
  rw [List.map_append]
  rw [sumInt_append]
  have hbad := sumInt_pair_zero P.badPairs P.size P.opposite
  have hbad_map :
      sumInt ((P.badPairs.flatMap (fun p => [p.1, p.2])).map
        (fun a => paritySign (P.size a))) = 0 := by
    rw [List.map_flatMap]
    exact hbad
  rw [hbad_map]
  simp

/-!
  This is the graph-ledger reading of the preceding certificate.  Once the
  finite graph construction supplies the pairing decomposition, `m` is the
  signed connected-subgraph sum and `good` is exactly the unpaired NBC-tree
  list.  No external combinatorial theorem is used by this composition.
-/
/-- The alternating signed count of the listed connected subgraphs. -/
def signedConnectedLedger {A : Type} (connectedSubgraphs : List A)
    (size : A -> Nat) : Int :=
  signedList connectedSubgraphs size

/-- The alternating signed count of the listed no-broken-circuit trees. -/
def nbcTreeLedger {A : Type} (nbcTrees : List A) (size : A -> Nat) : Int :=
  signedList nbcTrees size

theorem signed_connected_ledger_eq_nbc_tree_ledger {A : Type}
    (P : NBCPairing A) :
    signedConnectedLedger P.all P.size =
      nbcTreeLedger P.good P.size := by
  exact signed_sum_of_nbc_pairing P

/-- The number of listed surviving trees multiplied by the common rank-parity sign. -/
def nbcSignedCount {A : Type} (trees : List A) (rank : Nat) : Int :=
  sumInt (trees.map (fun _ => paritySign rank))

theorem signed_connected_ledger_eq_nbc_signed_count {A : Type}
    (P : NBCPairing A) :
    signedConnectedLedger P.all P.size =
      nbcSignedCount P.good P.rank := by
  rw [signed_connected_ledger_eq_nbc_tree_ledger P]
  exact signedList_eq_constant P.good P.size P.rank P.goodParity

end HsVirial
