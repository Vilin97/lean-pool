/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Linear

/-!
# Transport and exhaustion (A6)

Statements split from the original `Statements.lean` skeleton (one file per proving task).
The mathematics is AUDIT-NOTES A6, with the paper proofs in sections 12 (`lem:transport`) and
13 (`lem:exhaustion`).

Both statements are proved. `induced_transport` is split into its two halves,
`transport_ai_feasible` (an `H`-witness extends to a `G`-witness) and
`transport_compatible_restrict` (a `G`-model restricts to an `H`-model); the `Transport`
namespace carries their machinery, and the `Exhaustion` namespace the graph theory behind
`exhaustion`. Both namespaces are nested so that their generic names cannot collide with the
rest of the library.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## A6: transport along induced subgraphs, and exhaustion -/

/-! ### Infrastructure for transport

The machinery of `lem:transport`, kept in the `Transport` namespace so that its generic names do
not collide with the rest of the library: pushforward algebra and pi-type splitting, the edge map
of an induced embedding, the extended witness (`transportWitness`) with its symmetry, diagonal
law and ancestral prescriptions, and the restricted model (`restrictModel`) with its validity and
observed law. -/

namespace Transport

/-! ## Generic lemmas -/

theorem sum_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) :
    ∑ y : (∀ i, α i), ∏ i, w i (y i) = ∏ i, ∑ a, w i a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem sum_respMass (q : ℝ) : ∑ b : Bool, respMass q b = 1 := by
  simp [respMass]

theorem cast_pi_apply {ι : Type*} {α : ι → Type*} (x : ∀ i, α i) {a b : ι} (p : a = b) :
    cast (congrArg α p) (x a) = x b := by subst p; rfl

theorem cast_inj_apply {ι ι' : Type*} {α : ι → Type*} (F : ι' → ι) (hF : Function.Injective F)
    (x : ∀ f, α (F f)) {f' f : ι'} (p : F f' = F f) :
    cast (congrArg α p) (x f') = x f := by
  obtain rfl := hF p; rfl

/-- `respMass` is affine in its first argument. -/
theorem respMass_affine {ι : Type*} [Fintype ι] (w : ι → ℝ) (q : ι → ℝ) (b : Bool)
    (hw : ∑ i, w i = 1) :
    ∑ i, w i * respMass (q i) b = respMass (∑ i, w i * q i) b := by
  cases b
  · simp [respMass]
  · simp only [respMass, ite_true]
    have h : ∀ i ∈ (Finset.univ : Finset ι), w i * (1 - q i) = w i - w i * q i :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, hw]

/-- Splitting a product over a finite type along a predicate. -/
theorem prod_split {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (F : ι → ℝ) :
    ∏ i, F i = (∏ i : {x : ι // p x}, F i.1) * (∏ i : {x : ι // ¬ p x}, F i.1) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ p F]
  congr 1
  · exact Finset.prod_subtype _ (by intro x; simp) _
  · exact Finset.prod_subtype _ (by intro x; simp) _

/-! ## Splitting a sum over a dependent function type along a predicate -/

/-- Reassemble a dependent function from its restrictions to `p` and to `¬ p`. -/
def piMerge {ι : Type*} (p : ι → Prop) [DecidablePred p] (α : ι → Type*)
    (a : ∀ i : {x : ι // p x}, α i) (b : ∀ i : {x : ι // ¬ p x}, α i) : ∀ i, α i :=
  fun i => if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩

/-- The corresponding equivalence. -/
def piSplitEquiv {ι : Type*} (p : ι → Prop) [DecidablePred p] (α : ι → Type*) :
    ((∀ i : {x : ι // p x}, α i) × (∀ i : {x : ι // ¬ p x}, α i)) ≃ (∀ i, α i) where
  toFun q := piMerge p α q.1 q.2
  invFun z := (fun i => z i.1, fun i => z i.1)
  left_inv := by
    rintro ⟨a, b⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext i; simp [piMerge, i.2]
    · funext i; simp [piMerge, i.2]
  right_inv := by
    intro z; funext i; by_cases h : p i <;> simp [piMerge, h]

theorem sum_sum_prod {κ ν : Type*} [Fintype κ] [Fintype ν] (Pa : κ → ℝ) (Pb : ν → ℝ)
    (ha : ∑ a, Pa a = 1) (hb : ∑ b, Pb b = 1) (f : κ → ℝ) (g : ν → ℝ) :
    (∑ a, ∑ b, (Pa a * Pb b) * (f a * g b))
      = (∑ a, ∑ b, (Pa a * Pb b) * f a) * (∑ a, ∑ b, (Pa a * Pb b) * g b) := by
  have h1 : (∑ a, ∑ b, (Pa a * Pb b) * f a) = ∑ a, Pa a * f a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset ν)) =>
      show (Pa a * Pb b) * f a = (Pa a * f a) * Pb b by ring), ← Finset.mul_sum, hb, mul_one]
  have h2 : (∑ a, ∑ b, (Pa a * Pb b) * g b) = ∑ b, Pb b * g b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset κ)) =>
      show (Pa a * Pb b) * g b = (Pb b * g b) * Pa a by ring), ← Finset.mul_sum, ha, mul_one]
  have h3 : (∑ a, ∑ b, (Pa a * Pb b) * (f a * g b))
      = ∑ a, ∑ b, (Pa a * f a) * (Pb b * g b) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  rw [h1, h2, h3, Finset.sum_mul_sum]

theorem sum_sum_prod' {κ ν : Type*} [Fintype κ] [Fintype ν] (Pa : κ → ℝ) (Pb : ν → ℝ)
    (ha : ∑ a, Pa a = 1) (hb : ∑ b, Pb b = 1) (A B : κ → ν → ℝ)
    (hA : ∀ a b b', A a b = A a b') (hB : ∀ a a' b, B a b = B a' b) :
    (∑ a, ∑ b, (Pa a * Pb b) * (A a b * B a b))
      = (∑ a, ∑ b, (Pa a * Pb b) * A a b) * (∑ a, ∑ b, (Pa a * Pb b) * B a b) := by
  have hF : ∀ a b, A a b = ∑ b', Pb b' * A a b' := by
    intro a b
    calc A a b = (∑ b', Pb b') * A a b := by rw [hb, one_mul]
      _ = ∑ b', Pb b' * A a b := by rw [Finset.sum_mul]
      _ = ∑ b', Pb b' * A a b' := Finset.sum_congr rfl (fun b' _ => by rw [hA a b b'])
  have hG : ∀ a b, B a b = ∑ a', Pa a' * B a' b := by
    intro a b
    calc B a b = (∑ a', Pa a') * B a b := by rw [ha, one_mul]
      _ = ∑ a', Pa a' * B a b := by rw [Finset.sum_mul]
      _ = ∑ a', Pa a' * B a' b := Finset.sum_congr rfl (fun a' _ => by rw [hB a a' b])
  calc (∑ a, ∑ b, (Pa a * Pb b) * (A a b * B a b))
      = ∑ a, ∑ b, (Pa a * Pb b) * ((∑ b', Pb b' * A a b') * (∑ a', Pa a' * B a' b)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [← hF, ← hG]))
    _ = (∑ a, ∑ b, (Pa a * Pb b) * (∑ b', Pb b' * A a b'))
          * (∑ a, ∑ b, (Pa a * Pb b) * (∑ a', Pa a' * B a' b)) := sum_sum_prod Pa Pb ha hb _ _
    _ = (∑ a, ∑ b, (Pa a * Pb b) * A a b) * (∑ a, ∑ b, (Pa a * Pb b) * B a b) := by
        congr 1
        · exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [← hF]))
        · exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [← hG]))

theorem sum_pi_two_block {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)]
    (p : ι → Prop) [DecidablePred p] (w : ∀ i, α i → ℝ) (hw : ∀ i, ∑ a, w i a = 1)
    (A B : (∀ i, α i) → ℝ)
    (hA : ∀ z z' : (∀ i, α i), (∀ i, p i → z i = z' i) → A z = A z')
    (hB : ∀ z z' : (∀ i, α i), (∀ i, ¬ p i → z i = z' i) → B z = B z') :
    (∑ z : (∀ i, α i), (∏ i, w i (z i)) * (A z * B z))
      = (∑ z : (∀ i, α i), (∏ i, w i (z i)) * A z)
        * (∑ z : (∀ i, α i), (∏ i, w i (z i)) * B z) := by
  have hprod : ∀ (a : ∀ i : {x : ι // p x}, α i) (b : ∀ i : {x : ι // ¬ p x}, α i),
      (∏ i, w i (piMerge p α a b i))
        = (∏ i : {x : ι // p x}, w i.1 (a i)) * (∏ i : {x : ι // ¬ p x}, w i.1 (b i)) := by
    intro a b
    rw [prod_split p (fun i => w i (piMerge p α a b i))]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by simp [piMerge, i.2])
    · exact Finset.prod_congr rfl (fun i _ => by simp [piMerge, i.2])
  have key : ∀ F : (∀ i, α i) → ℝ,
      (∑ z : (∀ i, α i), (∏ i, w i (z i)) * F z)
        = ∑ a : (∀ i : {x : ι // p x}, α i), ∑ b : (∀ i : {x : ι // ¬ p x}, α i),
            ((∏ i : {x : ι // p x}, w i.1 (a i)) * (∏ i : {x : ι // ¬ p x}, w i.1 (b i)))
              * F (piMerge p α a b) := by
    intro F
    rw [← Equiv.sum_comp (piSplitEquiv p α) (fun z => (∏ i, w i (z i)) * F z),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      rw [show (piSplitEquiv p α) (a, b) = piMerge p α a b from rfl, hprod]))
  have hsa : ∑ a : (∀ i : {x : ι // p x}, α i), (∏ i : {x : ι // p x}, w i.1 (a i)) = 1 := by
    rw [sum_prod_pi (fun i : {x : ι // p x} => w i.1)]
    exact Finset.prod_eq_one (fun i _ => hw i.1)
  have hsb : ∑ b : (∀ i : {x : ι // ¬ p x}, α i), (∏ i : {x : ι // ¬ p x}, w i.1 (b i)) = 1 := by
    rw [sum_prod_pi (fun i : {x : ι // ¬ p x} => w i.1)]
    exact Finset.prod_eq_one (fun i _ => hw i.1)
  rw [key (fun z => A z * B z), key A, key B]
  exact sum_sum_prod' _ _ hsa hsb (fun a b => A (piMerge p α a b)) (fun a b => B (piMerge p α a b))
    (fun a b b' => hA _ _ (fun i hi => by simp [piMerge, hi]))
    (fun a a' b => hB _ _ (fun i hi => by simp [piMerge, hi]))

/-- Independence: the expectation of a product of functions of disjoint blocks of coordinates
factorizes. -/
theorem sum_pi_prod_indep {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)]
    {ν : Type*} [DecidableEq ν] (blk : ν → ι → Prop) [∀ u, DecidablePred (blk u)]
    (w : ∀ i, α i → ℝ) (hw : ∀ i, ∑ a, w i a = 1)
    (g : ν → (∀ i, α i) → ℝ)
    (hdisj : ∀ u u' : ν, u ≠ u' → ∀ i, blk u i → ¬ blk u' i)
    (hg : ∀ u, ∀ z z' : (∀ i, α i), (∀ i, blk u i → z i = z' i) → g u z = g u z')
    (s : Finset ν) :
    (∑ z : (∀ i, α i), (∏ i, w i (z i)) * ∏ u ∈ s, g u z)
      = ∏ u ∈ s, (∑ z : (∀ i, α i), (∏ i, w i (z i)) * g u z) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, mul_one]
    rw [sum_prod_pi w]
    exact Finset.prod_eq_one (fun i _ => hw i)
  · intro u₀ s hu₀ ih
    simp only [Finset.prod_insert hu₀]
    rw [← ih]
    exact sum_pi_two_block (blk u₀) w hw (g u₀) (fun z => ∏ u ∈ s, g u z) (hg u₀)
      (fun z z' hzz' => Finset.prod_congr rfl (fun u hu =>
        hg u z z' (fun i hi => hzz' i (hdisj u u₀ (by rintro rfl; exact hu₀ hu) i hi))))

/-! ## The edge map of an induced embedding -/

/-- The edge map induced by an induced embedding. -/
def edgeMap (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) : H.Edge → G.Edge := fun e =>
  ⟨Sym2.map φ e.1, by
    obtain ⟨e, he⟩ := e
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet] at *
      exact (hind x y).1 he⟩

@[simp] theorem edgeMap_val (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (e : H.Edge) :
    (edgeMap G H φ hind e).1 = Sym2.map φ e.1 := rfl

theorem edgeMap_injective (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) :
    Function.Injective (edgeMap G H φ hind) := by
  intro a b hab
  apply Subtype.ext
  exact Sym2.map.injective hφ (congrArg Subtype.val hab)

/-- Inducedness gives the exact incidence correspondence. -/
theorem edgeMap_mem_inc_iff (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (u : H.V) (e : H.Edge) :
    edgeMap G H φ hind e ∈ G.inc (φ u) ↔ e ∈ H.inc u := by
  simp only [PairGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and, edgeMap_val,
    Sym2.mem_map]
  constructor
  · rintro ⟨w, hw, hwu⟩; rwa [hφ hwu] at hw
  · intro h; exact ⟨u, h, rfl⟩

/-- The `G`-edges outside the image of the edge map. -/
abbrev Rest (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) : Type :=
  {g : G.Edge // ¬ ∃ f : H.Edge, edgeMap G H φ hind f = g}

/-- Key consequence of inducedness: an edge of `G` outside the image of the edge map meets the
image of `φ` in at most one vertex. -/
theorem cross_unique (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (g : G.Edge)
    (hg : ¬ ∃ f : H.Edge, edgeMap G H φ hind f = g) (u u' : H.V)
    (hu : g ∈ G.inc (φ u)) (hu' : g ∈ G.inc (φ u')) : u = u' := by
  by_contra hne
  have hne' : φ u ≠ φ u' := fun h => hne (hφ h)
  simp only [PairGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
  have hz : (g : G.Edge).1 = s(φ u, φ u') := (Sym2.mem_and_mem_iff hne').1 ⟨hu, hu'⟩
  have hadjG : G.G.Adj (φ u) (φ u') := by
    have := g.2
    rw [SimpleGraph.mem_edgeFinset, hz, SimpleGraph.mem_edgeSet] at this
    exact this
  have hadjH : H.G.Adj u u' := (hind u u').2 hadjG
  exact hg ⟨⟨s(u, u'), by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadjH⟩,
    Subtype.ext (by rw [edgeMap_val, Sym2.map_mk, hz])⟩

/-! ## The restricted model -/

/-- Merge the `H`-edge values `c` at `u` with the values `z` of the remaining `G`-edges. -/
noncomputable def mergeVals (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) (u : H.V)
    (c : (f : H.inc u) → M.L (edgeMap G H φ hind f.1))
    (z : ∀ r : Rest G H φ hind, M.L r.1) :
    (g : G.inc (φ u)) → M.L g.1 := fun g =>
  if h : ∃ f : H.Edge, edgeMap G H φ hind f = g.1 then
    cast (congrArg M.L h.choose_spec)
      (c ⟨h.choose, by
        rw [← edgeMap_mem_inc_iff G H φ hφ hind u h.choose, h.choose_spec]
        exact g.2⟩)
  else z ⟨g.1, h⟩

theorem mergeVals_eq (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) (u : H.V)
    (X : ∀ g : G.Edge, M.L g) :
    (fun g : G.inc (φ u) => X g.1)
      = mergeVals G H φ hφ hind M u (fun f => X (edgeMap G H φ hind f.1)) (fun r => X r.1) := by
  funext g
  simp only [mergeVals]
  split
  · next h => exact (cast_pi_apply X h.choose_spec).symm
  · rfl

/-- The model of `H` obtained from a model of `G` by keeping the sources in the image of the
edge map and averaging out the remaining ones. -/
noncomputable def restrictModel (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) : GModel H where
  L := fun f => M.L (edgeMap G H φ hind f)
  fintypeL := fun _ => M.fintypeL _
  μ := fun f => M.μ (edgeMap G H φ hind f)
  resp := fun u c => ∑ z : (∀ r : Rest G H φ hind, M.L r.1),
    (∏ r : Rest G H φ hind, M.μ r.1 (z r)) * M.resp (φ u) (mergeVals G H φ hφ hind M u c z)

theorem restrictModel_valid (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) (hM : M.Valid) :
    (restrictModel G H φ hφ hind M).Valid := by
  have hnn : ∀ (z : ∀ r : Rest G H φ hind, M.L r.1),
      0 ≤ ∏ r : Rest G H φ hind, M.μ r.1 (z r) :=
    fun z => Finset.prod_nonneg (fun r _ => (hM.1 r.1).1 _)
  have htot : ∑ z : (∀ r : Rest G H φ hind, M.L r.1),
      (∏ r : Rest G H φ hind, M.μ r.1 (z r)) = 1 := by
    rw [sum_prod_pi (fun r : Rest G H φ hind => M.μ r.1)]
    exact Finset.prod_eq_one (fun r _ => (hM.1 r.1).2)
  refine ⟨fun _ => hM.1 _, fun u c => ⟨?_, ?_⟩⟩
  · exact Finset.sum_nonneg (fun z _ => mul_nonneg (hnn z) (hM.2 _ _).1)
  · calc (restrictModel G H φ hφ hind M).resp u c
        ≤ ∑ z : (∀ r : Rest G H φ hind, M.L r.1),
            (∏ r : Rest G H φ hind, M.μ r.1 (z r)) * 1 :=
          Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hM.2 _ _).2 (hnn z))
      _ = 1 := by simpa using htot

/-! ## Range equivalences and counting -/

/-- An injection is an equivalence onto its image, described as a subtype. -/
noncomputable def imgEquiv {A B : Type*} (F : A → B) (hF : Function.Injective F) :
    A ≃ {b : B // ∃ a, F a = b} where
  toFun a := ⟨F a, a, rfl⟩
  invFun b := b.2.choose
  left_inv a := hF (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', F a' = F a))
  right_inv b := Subtype.ext b.2.choose_spec

@[simp] theorem imgEquiv_val {A B : Type*} (F : A → B) (hF : Function.Injective F) (a : A) :
    (imgEquiv F hF a).1 = F a := rfl

theorem card_img {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (F : A → B)
    (hF : Function.Injective F) :
    Fintype.card {b : B // ∃ a, F a = b} = Fintype.card A :=
  (Fintype.card_congr (imgEquiv F hF)).symm

theorem card_compl_img {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (F : A → B)
    (hF : Function.Injective F) :
    Fintype.card {b : B // ¬ ∃ a, F a = b} = Fintype.card B - Fintype.card A := by
  rw [Fintype.card_subtype_compl, card_img F hF]

/-! ## The vertex-side splitting -/

/-- Splitting an outcome vector of `G` into its restriction along `φ` and the rest. -/
noncomputable def vtxEquiv (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ) :
    ((H.V → Bool) × ({v : G.V // ¬ ∃ u, φ u = v} → Bool)) ≃ (G.V → Bool) where
  toFun q := fun v => if h : ∃ u, φ u = v then q.1 h.choose else q.2 ⟨v, h⟩
  invFun w := (fun u => w (φ u), fun v => w v.1)
  left_inv := by
    rintro ⟨a, b⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext u
      have h : ∃ u', φ u' = φ u := ⟨u, rfl⟩
      rw [dite_eq_left h, hφ h.choose_spec]
    · funext v
      rw [dite_eq_right v.2]
  right_inv := by
    intro w
    funext v
    dsimp only
    by_cases h : ∃ u, φ u = v
    · rw [dite_eq_left h]; exact congrArg w h.choose_spec
    · rw [dite_eq_right h]

theorem vtxEquiv_phi (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (a : H.V → Bool) (b : {v : G.V // ¬ ∃ u, φ u = v} → Bool) (u : H.V) :
    vtxEquiv G H φ hφ (a, b) (φ u) = a u := by
  have h : ∃ u', φ u' = φ u := ⟨u, rfl⟩
  change (if h : ∃ u', φ u' = φ u then a h.choose else _) = a u
  rw [dite_eq_left h, hφ h.choose_spec]

theorem vtxEquiv_out (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (a : H.V → Bool) (b : {v : G.V // ¬ ∃ u, φ u = v} → Bool)
    (v : {v : G.V // ¬ ∃ u, φ u = v}) :
    vtxEquiv G H φ hφ (a, b) v.1 = b v := by
  change (if h : ∃ u', φ u' = v.1 then a h.choose else b ⟨v.1, h⟩) = b v
  rw [dite_eq_right v.2]

/-- Marginalizing a product over the vertices of `G` down to the vertices of `H`. -/
theorem vtx_marginal (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (q : G.V → ℝ) (wH : H.V → Bool) :
    (∑ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool),
        ∏ v : G.V, respMass (q v) (vtxEquiv G H φ hφ (wH, b) v))
      = ∏ u : H.V, respMass (q (φ u)) (wH u) := by
  have hsplit : ∀ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool),
      (∏ v : G.V, respMass (q v) (vtxEquiv G H φ hφ (wH, b) v))
        = (∏ u : H.V, respMass (q (φ u)) (wH u))
            * ∏ v : {v : G.V // ¬ ∃ u, φ u = v}, respMass (q v.1) (b v) := by
    intro b
    rw [prod_split (fun v : G.V => ∃ u, φ u = v)
      (fun v => respMass (q v) (vtxEquiv G H φ hφ (wH, b) v))]
    congr 1
    · exact (Fintype.prod_equiv (imgEquiv φ hφ) (fun u => respMass (q (φ u)) (wH u))
        (fun v : {v : G.V // ∃ u, φ u = v} => respMass (q v.1) (vtxEquiv G H φ hφ (wH, b) v.1))
        (fun u => by rw [imgEquiv_val, vtxEquiv_phi])).symm
    · refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [vtxEquiv_out]
  rw [Finset.sum_congr rfl (fun b _ => hsplit b), ← Finset.mul_sum,
    sum_prod_pi (fun (v : {v : G.V // ¬ ∃ u, φ u = v}) => fun c : Bool => respMass (q v.1) c),
    Finset.prod_eq_one (fun (v : {v : G.V // ¬ ∃ u, φ u = v}) _ => sum_respMass (q v.1)),
    mul_one]

/-! ## The edge-side splitting -/

/-- Splitting a joint value of all `G`-sources into the values on the image of the edge map and
the values on the rest. -/
noncomputable def edgeValEquiv (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) :
    ((∀ f : H.Edge, M.L (edgeMap G H φ hind f)) × (∀ r : Rest G H φ hind, M.L r.1))
      ≃ (∀ g : G.Edge, M.L g) where
  toFun q := fun g => if h : ∃ f : H.Edge, edgeMap G H φ hind f = g then
      cast (congrArg M.L h.choose_spec) (q.1 h.choose) else q.2 ⟨g, h⟩
  invFun X := (fun f => X (edgeMap G H φ hind f), fun r => X r.1)
  left_inv := by
    rintro ⟨x, z⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext f
      have h : ∃ f' : H.Edge, edgeMap G H φ hind f' = edgeMap G H φ hind f := ⟨f, rfl⟩
      rw [dite_eq_left h]
      exact cast_inj_apply (edgeMap G H φ hind) (edgeMap_injective G H φ hφ hind) x h.choose_spec
    · funext r
      rw [dite_eq_right r.2]
  right_inv := by
    intro X
    funext g
    dsimp only
    by_cases h : ∃ f : H.Edge, edgeMap G H φ hind f = g
    · rw [dite_eq_left h]; exact cast_pi_apply X h.choose_spec
    · rw [dite_eq_right h]

theorem edgeValEquiv_left (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G)
    (x : ∀ f : H.Edge, M.L (edgeMap G H φ hind f)) (z : ∀ r : Rest G H φ hind, M.L r.1)
    (f : H.Edge) :
    edgeValEquiv G H φ hφ hind M (x, z) (edgeMap G H φ hind f) = x f := by
  have h : ∃ f' : H.Edge, edgeMap G H φ hind f' = edgeMap G H φ hind f := ⟨f, rfl⟩
  change (if h : ∃ f' : H.Edge, edgeMap G H φ hind f' = edgeMap G H φ hind f then
      cast (congrArg M.L h.choose_spec) (x h.choose) else _) = x f
  rw [dite_eq_left h]
  exact cast_inj_apply (edgeMap G H φ hind) (edgeMap_injective G H φ hφ hind) x h.choose_spec

theorem edgeValEquiv_right (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G)
    (x : ∀ f : H.Edge, M.L (edgeMap G H φ hind f)) (z : ∀ r : Rest G H φ hind, M.L r.1)
    (r : Rest G H φ hind) :
    edgeValEquiv G H φ hφ hind M (x, z) r.1 = z r := by
  change (if h : ∃ f' : H.Edge, edgeMap G H φ hind f' = r.1 then
      cast (congrArg M.L h.choose_spec) (x h.choose) else z ⟨r.1, h⟩) = z r
  rw [dite_eq_right r.2]

theorem edgeValEquiv_prod (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G)
    (x : ∀ f : H.Edge, M.L (edgeMap G H φ hind f)) (z : ∀ r : Rest G H φ hind, M.L r.1) :
    (∏ g : G.Edge, M.μ g (edgeValEquiv G H φ hφ hind M (x, z) g))
      = (∏ f : H.Edge, M.μ (edgeMap G H φ hind f) (x f))
        * ∏ r : Rest G H φ hind, M.μ r.1 (z r) := by
  have h1 : (∏ g : {g : G.Edge // ∃ f : H.Edge, edgeMap G H φ hind f = g},
      M.μ g.1 (edgeValEquiv G H φ hφ hind M (x, z) g.1))
      = ∏ f : H.Edge, M.μ (edgeMap G H φ hind f) (x f) :=
    (Fintype.prod_equiv (imgEquiv (edgeMap G H φ hind) (edgeMap_injective G H φ hφ hind))
      (fun f => M.μ (edgeMap G H φ hind f) (x f))
      (fun g : {g : G.Edge // ∃ f : H.Edge, edgeMap G H φ hind f = g} =>
        M.μ g.1 (edgeValEquiv G H φ hφ hind M (x, z) g.1))
      (fun f => by rw [imgEquiv_val, edgeValEquiv_left])).symm
  have h2 : (∏ r : Rest G H φ hind, M.μ r.1 (edgeValEquiv G H φ hφ hind M (x, z) r.1))
      = ∏ r : Rest G H φ hind, M.μ r.1 (z r) :=
    Finset.prod_congr rfl (fun r _ => by rw [edgeValEquiv_right])
  rw [prod_split (fun g : G.Edge => ∃ f : H.Edge, edgeMap G H φ hind f = g)
    (fun g => M.μ g (edgeValEquiv G H φ hφ hind M (x, z) g)), h1, h2]

theorem mergeVals_edgeVal (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (M : GModel G) (u : H.V)
    (x : ∀ f : H.Edge, M.L (edgeMap G H φ hind f)) (z : ∀ r : Rest G H φ hind, M.L r.1) :
    (fun g : G.inc (φ u) => edgeValEquiv G H φ hφ hind M (x, z) g.1)
      = mergeVals G H φ hφ hind M u (fun f => x f.1) z := by
  have e1 : (fun f : H.inc u => edgeValEquiv G H φ hφ hind M (x, z) (edgeMap G H φ hind f.1))
      = (fun f : H.inc u => x f.1) :=
    funext (fun f => edgeValEquiv_left G H φ hφ hind M x z f.1)
  have e2 : (fun r : Rest G H φ hind => edgeValEquiv G H φ hφ hind M (x, z) r.1) = z :=
    funext (fun r => edgeValEquiv_right G H φ hφ hind M x z r)
  rw [mergeVals_eq G H φ hφ hind M u (edgeValEquiv G H φ hφ hind M (x, z)), e1, e2]

/-! ## The observed law of the restricted model -/

theorem restrictModel_law (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (P : GTarget H) (M : GModel G)
    (hM : M.Valid) (hlaw : M.law = transportTarget G H φ P) :
    (restrictModel G H φ hφ hind M).law = P := by
  have htot : ∑ z : (∀ r : Rest G H φ hind, M.L r.1),
      (∏ r : Rest G H φ hind, M.μ r.1 (z r)) = 1 := by
    rw [sum_prod_pi (fun r : Rest G H φ hind => M.μ r.1)]
    exact Finset.prod_eq_one (fun r _ => (hM.1 r.1).2)
  funext wH
  -- Step 1: marginalize the hypothesis over the vertices outside the image of `φ`.
  have step1 : (∑ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool),
      M.law (vtxEquiv G H φ hφ (wH, b))) = P wH := by
    have hval : ∀ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool),
        M.law (vtxEquiv G H φ hφ (wH, b))
          = P wH * (1/2 : ℝ) ^ (Fintype.card G.V - Fintype.card H.V) := by
      intro b
      have hfun : (fun u => vtxEquiv G H φ hφ (wH, b) (φ u)) = wH :=
        funext (fun u => vtxEquiv_phi G H φ hφ wH b u)
      rw [hlaw]
      change P (fun u => vtxEquiv G H φ hφ (wH, b) (φ u))
          * (1/2 : ℝ) ^ (Fintype.card G.V - Fintype.card H.V)
        = P wH * (1/2 : ℝ) ^ (Fintype.card G.V - Fintype.card H.V)
      rw [hfun]
    rw [Finset.sum_congr rfl (fun b _ => hval b), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, card_compl_img φ hφ, nsmul_eq_mul]
    push_cast
    rw [show ((2:ℝ) ^ (Fintype.card G.V - Fintype.card H.V))
          * (P wH * (1/2 : ℝ) ^ (Fintype.card G.V - Fintype.card H.V))
        = P wH * (((2:ℝ) * (1/2 : ℝ)) ^ (Fintype.card G.V - Fintype.card H.V)) by
      rw [mul_pow]; ring]
    norm_num
  -- Step 2: the resulting identity for `M`, with the outside vertices integrated away.
  have step2 : (∑ X : (∀ g : G.Edge, M.L g), (∏ g : G.Edge, M.μ g (X g))
      * ∏ u : H.V, respMass (M.resp (φ u) (fun e => X e.1)) (wH u)) = P wH := by
    rw [← step1, show (∑ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool),
        M.law (vtxEquiv G H φ hφ (wH, b)))
        = ∑ b : ({v : G.V // ¬ ∃ u, φ u = v} → Bool), ∑ X : (∀ g : G.Edge, M.L g),
            (∏ g : G.Edge, M.μ g (X g))
              * ∏ v : G.V, respMass (M.resp v (fun e => X e.1)) (vtxEquiv G H φ hφ (wH, b) v)
      from rfl, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [← Finset.mul_sum, vtx_marginal G H φ hφ (fun v => M.resp v (fun e => X e.1)) wH]
  -- Step 3: split the sum over the `G`-sources.
  have hterm : ∀ (x : ∀ f : H.Edge, M.L (edgeMap G H φ hind f))
      (z : ∀ r : Rest G H φ hind, M.L r.1),
      (∏ g : G.Edge, M.μ g (edgeValEquiv G H φ hφ hind M (x, z) g))
        * ∏ u : H.V, respMass (M.resp (φ u)
            (fun e => edgeValEquiv G H φ hφ hind M (x, z) e.1)) (wH u)
      = ((∏ f : H.Edge, M.μ (edgeMap G H φ hind f) (x f))
          * ∏ r : Rest G H φ hind, M.μ r.1 (z r))
        * ∏ u : H.V, respMass (M.resp (φ u)
            (mergeVals G H φ hφ hind M u (fun f => x f.1) z)) (wH u) := by
    intro x z
    have hu : ∀ u : H.V, (fun e : G.inc (φ u) => edgeValEquiv G H φ hφ hind M (x, z) e.1)
        = mergeVals G H φ hφ hind M u (fun f => x f.1) z :=
      fun u => mergeVals_edgeVal G H φ hφ hind M u x z
    simp only [hu]
    rw [edgeValEquiv_prod]
  rw [← step2, ← Equiv.sum_comp (edgeValEquiv G H φ hφ hind M)
      (fun X : (∀ g : G.Edge, M.L g) => (∏ g : G.Edge, M.μ g (X g))
        * ∏ u : H.V, respMass (M.resp (φ u) (fun e => X e.1)) (wH u)),
    Fintype.sum_prod_type,
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => hterm x z))]
  change (∑ x : (∀ f : H.Edge, M.L (edgeMap G H φ hind f)),
      (∏ f : H.Edge, M.μ (edgeMap G H φ hind f) (x f))
        * ∏ u : H.V, respMass ((restrictModel G H φ hφ hind M).resp u (fun e => x e.1)) (wH u))
    = _
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hdisj : ∀ u u' : H.V, u ≠ u' → ∀ r : Rest G H φ hind,
      r.1 ∈ G.inc (φ u) → ¬ (r.1 ∈ G.inc (φ u')) := by
    intro u u' hne r h1 h2
    exact hne (cross_unique G H φ hφ hind r.1 r.2 u u' h1 h2)
  have hgdep : ∀ (u : H.V) (z z' : ∀ r : Rest G H φ hind, M.L r.1),
      (∀ r : Rest G H φ hind, r.1 ∈ G.inc (φ u) → z r = z' r) →
      respMass (M.resp (φ u) (mergeVals G H φ hφ hind M u (fun f => x f.1) z)) (wH u)
        = respMass (M.resp (φ u) (mergeVals G H φ hφ hind M u (fun f => x f.1) z')) (wH u) := by
    intro u z z' hzz'
    have hmm : mergeVals G H φ hφ hind M u (fun f => x f.1) z
        = mergeVals G H φ hφ hind M u (fun f => x f.1) z' := by
      funext g
      simp only [mergeVals]
      split
      · rfl
      · next h => exact hzz' ⟨g.1, h⟩ g.2
    rw [hmm]
  have haff : ∀ u : H.V,
      respMass ((restrictModel G H φ hφ hind M).resp u (fun e => x e.1)) (wH u)
        = ∑ z : (∀ r : Rest G H φ hind, M.L r.1), (∏ r : Rest G H φ hind, M.μ r.1 (z r))
            * respMass (M.resp (φ u)
                (mergeVals G H φ hφ hind M u (fun f => x f.1) z)) (wH u) :=
    fun u => (respMass_affine (fun z : (∀ r : Rest G H φ hind, M.L r.1) =>
        ∏ r : Rest G H φ hind, M.μ r.1 (z r))
      (fun z => M.resp (φ u) (mergeVals G H φ hφ hind M u (fun f => x f.1) z)) (wH u) htot).symm
  rw [Finset.prod_congr rfl (fun u (_ : u ∈ (Finset.univ : Finset H.V)) => haff u),
    ← sum_pi_prod_indep (fun (u : H.V) (r : Rest G H φ hind) => r.1 ∈ G.inc (φ u))
      (fun r : Rest G H φ hind => M.μ r.1) (fun r => (hM.1 r.1).2)
      (fun (u : H.V) (z : ∀ r : Rest G H φ hind, M.L r.1) =>
        respMass (M.resp (φ u) (mergeVals G H φ hφ hind M u (fun f => x f.1) z)) (wH u))
      hdisj hgdep Finset.univ,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => by ring)


/-! Everything the transport proof needs beyond `Defs` lives in this namespace, so that the
generic names do not collide with the rest of the library. -/

namespace TransportFeasible

/-! ## Generic pushforward infrastructure -/

/-- Pushforwards compose. -/
theorem pushforward_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (w : α → ℝ) (F : α → β) (K : β → γ) :
    pushforward (pushforward w F) K = pushforward w (K ∘ F) := by
  funext c
  simp only [pushforward, Function.comp_apply]
  have h : ∀ b : β, (if K b = c then ∑ a, if F a = b then w a else 0 else 0)
      = ∑ a, (if K b = c then (if F a = b then w a else 0) else 0) := by
    intro b; split <;> simp
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (F a) (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp

/-- A pushforward of a law is a law. -/
theorem isLaw_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {w : α → ℝ} (h : IsLaw w) (F : α → β) : IsLaw (pushforward w F) := by
  refine ⟨fun b => Finset.sum_nonneg fun a _ => ?_, ?_⟩
  · by_cases hh : F a = b <;> simp [hh, h.1 a]
  · simp only [pushforward]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact h.2

/-- A product of laws is a law. -/
theorem isLaw_prod {A B : Type*} [Fintype A] [Fintype B] {w₁ : A → ℝ} {w₂ : B → ℝ}
    (h₁ : IsLaw w₁) (h₂ : IsLaw w₂) : IsLaw (fun p : A × B => w₁ p.1 * w₂ p.2) := by
  refine ⟨fun p => mul_nonneg (h₁.1 _) (h₂.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, h₂.2, mul_one]
  exact h₁.2

/-- A pushforward of a product law along a product map, evaluated at a pair of targets. -/
theorem pushforward_prod_apply {A B C D : Type*} [Fintype A] [Fintype B]
    [DecidableEq C] [DecidableEq D] (w₁ : A → ℝ) (w₂ : B → ℝ) (K₁ : A → C) (K₂ : B → D)
    (c : C) (d : D) :
    (∑ p : A × B, if K₁ p.1 = c ∧ K₂ p.2 = d then w₁ p.1 * w₂ p.2 else 0)
      = pushforward w₁ K₁ c * pushforward w₂ K₂ d := by
  simp only [pushforward, Fintype.sum_prod_type, ite_and, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : K₁ a = c
  · simp only [h, ite_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by by_cases h2 : K₂ b = d <;> simp [h2]
  · simp [h]

/-! ## The uniform law on a finite set of fair bits -/

/-- The law of independent fair bits indexed by `A`. -/
noncomputable def unifLaw (A : Type*) [Fintype A] : (A → Bool) → ℝ :=
  fun _ => (1 / 2 : ℝ) ^ (Fintype.card A)

theorem unifLaw_isLaw (A : Type*) [Fintype A] [DecidableEq A] : IsLaw (unifLaw A) := by
  refine ⟨fun _ => by simp only [unifLaw]; positivity, ?_⟩
  simp only [unifLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_bool]
  push_cast
  rw [← mul_pow]
  norm_num

/-- Restricting independent fair bits along an injection again gives independent fair bits. -/
theorem unifLaw_restrict {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : B → A) (hρ : Function.Injective ρ) :
    pushforward (unifLaw A) (fun ξ => fun b => ξ (ρ b)) = unifLaw B := by
  funext η
  simp only [pushforward, unifLaw]
  have key : ∀ ξ : A → Bool,
      (if (fun b => ξ (ρ b)) = η then ((1:ℝ) / 2) ^ Fintype.card A else 0)
        = ∏ a : A, ((1 / 2 : ℝ) *
            ∏ b : B, (if ρ b = a then (if ξ a = η b then (1:ℝ) else 0) else 1)) := by
    intro ξ
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_comm]
    have h1 : ∀ b : B, (∏ a : A, (if ρ b = a then (if ξ a = η b then (1:ℝ) else 0) else 1))
        = (if ξ (ρ b) = η b then (1:ℝ) else 0) := by
      intro b
      rw [Finset.prod_ite_eq]
      simp
    rw [Finset.prod_congr rfl (fun b _ => h1 b), Finset.prod_boole]
    have hiff : (∀ b ∈ (Finset.univ : Finset B), ξ (ρ b) = η b) ↔ ((fun b => ξ (ρ b)) = η) := by
      simp [funext_iff]
    by_cases hc : (fun b => ξ (ρ b)) = η
    · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc), mul_one]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h)), mul_zero]
  rw [Finset.sum_congr rfl (fun ξ _ => key ξ),
    sum_prod_pi (ι := A) (α := fun _ => Bool)
      (fun a x => (1 / 2 : ℝ) * ∏ b : B, (if ρ b = a then (if x = η b then (1:ℝ) else 0) else 1))]
  have h3 : ∀ a : A,
      (∑ x : Bool, (1 / 2 : ℝ) * ∏ b : B, (if ρ b = a then (if x = η b then (1:ℝ) else 0) else 1))
        = if a ∈ Finset.image ρ Finset.univ then (1 / 2 : ℝ) else 1 := by
    intro a
    by_cases ha : a ∈ Finset.image ρ Finset.univ
    · obtain ⟨b₀, -, hb₀⟩ := Finset.mem_image.1 ha
      have hp : ∀ x : Bool,
          (∏ b : B, (if ρ b = a then (if x = η b then (1:ℝ) else 0) else 1))
            = (if x = η b₀ then (1:ℝ) else 0) := by
        intro x
        rw [Finset.prod_eq_single b₀ (by
          intro b _ hb
          have : ρ b ≠ a := by
            intro hc; exact hb (hρ (hc.trans hb₀.symm))
          simp [this]) (by simp)]
        simp [hb₀]
      rw [ite_eq_left ha]
      simp only [hp, Fintype.sum_bool]
      cases η b₀ <;> norm_num
    · have hp : ∀ x : Bool,
          (∏ b : B, (if ρ b = a then (if x = η b then (1:ℝ) else 0) else 1)) = 1 := by
        intro x
        refine Finset.prod_eq_one fun b _ => ?_
        have : ρ b ≠ a := fun hc => ha (Finset.mem_image.2 ⟨b, Finset.mem_univ b, hc⟩)
        simp [this]
      rw [ite_eq_right ha]
      simp only [hp, Fintype.sum_bool]
      norm_num
  rw [Finset.prod_congr rfl (fun a _ => h3 a), ← Finset.prod_filter, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter (fun a => a ∈ Finset.image ρ Finset.univ)) = Finset.image ρ Finset.univ := by
    ext a; simp
  rw [this, Finset.card_image_of_injective _ hρ, Finset.card_univ]


/-! ## The induced edge map -/

theorem edgeMap_mem_inc (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (u : H.V) (e : H.Edge)
    (he : e ∈ H.inc u) : edgeMap G H φ hind e ∈ G.inc (φ u) := by
  simp only [PairGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact Sym2.mem_map.2 ⟨u, he, rfl⟩

/-- Every vertex is incident to a source. -/
theorem inc_nonempty (Γ : PairGraph) (v : Γ.V) : (Γ.inc v).Nonempty := by
  obtain ⟨w, hw⟩ := Γ.no_isolated v
  refine ⟨⟨s(v, w), ?_⟩, ?_⟩
  · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hw
  · simp [PairGraph.inc]

/-! ## Observations outside the image -/

/-- A vertex of `G` lies in the image of the embedding. -/
def InRange (G H : PairGraph) (φ : H.V → G.V) (v : G.V) : Prop := ∃ u : H.V, φ u = v

instance instDecidableInRange (G H : PairGraph) (φ : H.V → G.V) (v : G.V) :
    Decidable (InRange G H φ v) := inferInstanceAs (Decidable (∃ u : H.V, φ u = v))

/-- The copied observations of `G` at vertices outside the image of `φ`. -/
abbrev OutObs (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) :=
  {o : GObs G t // ¬ InRange G H φ o.1}

/-- The vertices of `G` outside the image of `φ`. -/
abbrev OutVert (G H : PairGraph) (φ : H.V → G.V) := {v : G.V // ¬ InRange G H φ v}

example (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) : Fintype (OutObs G H φ t) := inferInstance
example (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) : DecidableEq (OutObs G H φ t) := inferInstance
example (G H : PairGraph) (φ : H.V → G.V) : Fintype (OutVert G H φ) := inferInstance

/-- The `H`-observation that a `G`-observation at an image vertex reads: it keeps only the
copy indices of the sources coming from `H`. -/
def pullObs (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (o : GObs G t) (u : H.V) (h : φ u = o.1) : GObs H t :=
  ⟨u, fun f => o.2 ⟨edgeMap G H φ hind f.1, by
      have hm := edgeMap_mem_inc G H φ hind u f.1 f.2
      rwa [h] at hm⟩⟩

theorem pullObs_congr (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (o : GObs G t) (u u' : H.V) (h : φ u = o.1) (h' : φ u' = o.1) (huu : u = u') :
    pullObs G H φ hind t o u h = pullObs G H φ hind t o u' h' := by
  subst huu; rfl

/-- The extension of an `H`-witness assignment together with a family of outside fair bits to
a `G`-witness assignment. -/
noncomputable def extAssign (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) : GAssign G t := fun o =>
  if h : InRange G H φ o.1 then p.1 (pullObs G H φ hind t o h.choose h.choose_spec)
  else p.2 ⟨o, h⟩

theorem extAssign_in (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (o : GObs G t) (u : H.V) (h : φ u = o.1) :
    extAssign G H φ hind t p o = p.1 (pullObs G H φ hind t o u h) := by
  have hr : InRange G H φ o.1 := ⟨u, h⟩
  rw [extAssign, dite_eq_left hr]
  exact congrArg p.1
    (pullObs_congr G H φ hind t o _ u hr.choose_spec h (hφ (hr.choose_spec.trans h.symm)))

theorem extAssign_out (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (o : GObs G t) (h : ¬ InRange G H φ o.1) :
    extAssign G H φ hind t p o = p.2 ⟨o, h⟩ := by
  rw [extAssign, dite_eq_right h]


/-! ## The transported witness -/

/-- The law on the source type of the extension: an `H`-witness, and one independent fair bit
for every copied observation of `G` outside the image of `φ`. -/
noncomputable def transportSource (G H : PairGraph) (φ : H.V → G.V) (t : ℕ)
    (ΔH : GAssign H t → ℝ) : (GAssign H t × (OutObs G H φ t → Bool)) → ℝ :=
  fun p => ΔH p.1 * unifLaw (OutObs G H φ t) p.2

/-- The transported witness: the pushforward of `transportSource` along the extension map. -/
noncomputable def transportWitness (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (ΔH : GAssign H t → ℝ) : GAssign G t → ℝ :=
  pushforward (transportSource G H φ t ΔH) (extAssign G H φ hind t)

theorem transportSource_isLaw (G H : PairGraph) (φ : H.V → G.V) (t : ℕ)
    {ΔH : GAssign H t → ℝ} (h : IsLaw ΔH) : IsLaw (transportSource G H φ t ΔH) :=
  isLaw_prod h (unifLaw_isLaw _)

theorem transportWitness_isLaw (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    {ΔH : GAssign H t → ℝ} (h : IsLaw ΔH) : IsLaw (transportWitness G H φ hind t ΔH) :=
  isLaw_pushforward (transportSource_isLaw G H φ t h) _

/-! ## The diagonal law -/

/-- The diagonal copied observation of an outside vertex in row `r`. -/
def diagOutObs (G H : PairGraph) (φ : H.V → G.V) (t : ℕ)
    (q : Fin t × OutVert G H φ) : OutObs G H φ t := ⟨⟨q.2.1, fun _ => q.1⟩, q.2.2⟩

theorem diagOutObs_injective (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) :
    Function.Injective (diagOutObs G H φ t) := by
  rintro ⟨r, w, hw⟩ ⟨r', w', hw'⟩ h
  have h1 : (⟨w, fun _ => r⟩ : GObs G t) = ⟨w', fun _ => r'⟩ := congrArg Subtype.val h
  injection h1 with hv hfn
  subst hv
  rw [heq_iff_eq] at hfn
  obtain ⟨e, he⟩ := inc_nonempty G w
  have hr : r = r' := congrFun hfn ⟨e, he⟩
  subst hr
  rfl

theorem extAssign_diag_in (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (r : Fin t) (u : H.V) :
    extAssign G H φ hind t p (copyObs (fun _ => r) (φ u)) = readDiag p.1 r u := by
  rw [extAssign_in G H φ hφ hind t p _ u rfl]
  rfl

theorem extAssign_diag_out (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (r : Fin t) (w : OutVert G H φ) :
    extAssign G H φ hind t p (copyObs (fun _ => r) w.1) = p.2 (diagOutObs G H φ t (r, w)) := by
  rw [extAssign_out G H φ hind t p _ w.2]
  rfl

theorem readDiag_extAssign_iff (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (v : Fin t → G.V → Bool) :
    readDiag (extAssign G H φ hind t p) = v ↔
      (readDiag p.1 = fun r u => v r (φ u)) ∧
        ((fun q : Fin t × OutVert G H φ => p.2 (diagOutObs G H φ t q)) = fun q => v q.1 q.2.1) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext r u
      rw [← extAssign_diag_in G H φ hφ hind t p r u]
      exact congrFun (congrFun h r) (φ u)
    · funext q
      obtain ⟨r, w⟩ := q
      rw [← extAssign_diag_out G H φ hind t p r w]
      exact congrFun (congrFun h r) w.1
  · rintro ⟨h1, h2⟩
    funext r w
    by_cases hw : InRange G H φ w
    · obtain ⟨u, rfl⟩ := hw
      change extAssign G H φ hind t p (copyObs (fun _ => r) (φ u)) = v r (φ u)
      rw [extAssign_diag_in G H φ hφ hind t p r u]
      exact congrFun (congrFun h1 r) u
    · change extAssign G H φ hind t p (copyObs (fun _ => r) w) = v r w
      rw [extAssign_diag_out G H φ hind t p r ⟨w, hw⟩]
      exact congrFun h2 (r, ⟨w, hw⟩)

theorem card_outVert (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ) :
    Fintype.card (OutVert G H φ) = Fintype.card G.V - Fintype.card H.V := by
  have hbij : Function.Bijective
      (fun u : H.V => (⟨φ u, ⟨u, rfl⟩⟩ : {v : G.V // InRange G H φ v})) := by
    constructor
    · intro a b hab; exact hφ (congrArg Subtype.val hab)
    · rintro ⟨v, u, rfl⟩; exact ⟨u, rfl⟩
  have h1 : Fintype.card {v : G.V // InRange G H φ v} = Fintype.card H.V :=
    (Fintype.card_of_bijective hbij).symm
  rw [Fintype.card_subtype_compl, h1]

theorem transport_diag (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ) (P : GTarget H)
    (ΔH : GAssign H t → ℝ) (hdiag : pushforward ΔH readDiag = gTensorPow t P) :
    pushforward (transportWitness G H φ hind t ΔH) readDiag
      = gTensorPow t (transportTarget G H φ P) := by
  rw [transportWitness, pushforward_comp]
  funext v
  simp only [pushforward, Function.comp_apply, transportSource]
  have step : (∑ p : GAssign H t × (OutObs G H φ t → Bool),
        if readDiag (extAssign G H φ hind t p) = v then
          ΔH p.1 * unifLaw (OutObs G H φ t) p.2 else 0)
      = pushforward ΔH readDiag (fun r u => v r (φ u))
        * pushforward (unifLaw (OutObs G H φ t))
            (fun ξ => fun q => ξ (diagOutObs G H φ t q)) (fun q => v q.1 q.2.1) := by
    rw [← pushforward_prod_apply]
    exact Finset.sum_congr rfl fun p _ =>
      if_congr (readDiag_extAssign_iff G H φ hφ hind t p v) rfl rfl
  rw [step, hdiag, unifLaw_restrict _ (diagOutObs_injective G H φ t)]
  simp only [gTensorPow, transportTarget, unifLaw]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_fin, card_outVert G H φ hφ, mul_comm t _, pow_mul]


/-! ## Symmetry -/

/-- The action of a per-source permutation of copy indices, as an equivalence. -/
def gPermEquiv {Γ : PairGraph} {t : ℕ} (π : Γ.Edge → Equiv.Perm (Fin t)) :
    GObs Γ t ≃ GObs Γ t :=
  Equiv.sigmaCongrRight (fun _ => Equiv.piCongrRight (fun e => π e.1))

theorem gPermEquiv_apply {Γ : PairGraph} {t : ℕ} (π : Γ.Edge → Equiv.Perm (Fin t))
    (o : GObs Γ t) : gPermEquiv π o = gPerm π o := rfl

/-- Precomposition with an equivalence of the index type. -/
def precompEquiv {α β : Type*} (e : α ≃ α) : (α → β) ≃ (α → β) where
  toFun f := fun a => f (e a)
  invFun f := fun a => f (e.symm a)
  left_inv f := by funext a; simp
  right_inv f := by funext a; simp

theorem gRelabel_injective {Γ : PairGraph} {t : ℕ} (π : Γ.Edge → Equiv.Perm (Fin t)) :
    Function.Injective (gRelabel π) := by
  intro ω ω' h
  funext o
  have h2 := congrFun h ((gPermEquiv π).symm o)
  have e1 : gPerm π ((gPermEquiv π).symm o) = o := (gPermEquiv π).apply_symm_apply o
  simpa [gRelabel, e1] using h2

/-- Copy-index permutations act on the outside observations. -/
def outPermEquiv (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) (π : G.Edge → Equiv.Perm (Fin t)) :
    OutObs G H φ t ≃ OutObs G H φ t :=
  Equiv.subtypeEquiv (gPermEquiv π) (fun _ => Iff.rfl)

/-- The action of a `G`-permutation on the source type of the extension. -/
def srcPermEquiv (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (π : G.Edge → Equiv.Perm (Fin t)) :
    (GAssign H t × (OutObs G H φ t → Bool)) ≃ (GAssign H t × (OutObs G H φ t → Bool)) :=
  Equiv.prodCongr (precompEquiv (gPermEquiv (fun f : H.Edge => π (edgeMap G H φ hind f))))
    (precompEquiv (outPermEquiv G H φ t π))

theorem extAssign_relabel (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (π : G.Edge → Equiv.Perm (Fin t)) (p : GAssign H t × (OutObs G H φ t → Bool)) :
    extAssign G H φ hind t (srcPermEquiv G H φ hind t π p)
      = gRelabel π (extAssign G H φ hind t p) := by
  funext o
  have hgr : gRelabel π (extAssign G H φ hind t p) o
      = extAssign G H φ hind t p (gPerm π o) := rfl
  by_cases h : InRange G H φ o.1
  · obtain ⟨u, hu⟩ := h
    rw [extAssign_in G H φ hφ hind t _ o u hu, hgr,
      extAssign_in G H φ hφ hind t p (gPerm π o) u hu]
    rfl
  · rw [extAssign_out G H φ hind t _ o h, hgr, extAssign_out G H φ hind t p (gPerm π o) h]
    rfl

theorem transport_symmetric (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (ΔH : GAssign H t → ℝ) (hsym : GSymmetric t ΔH) :
    GSymmetric t (transportWitness G H φ hind t ΔH) := by
  intro π ω
  simp only [transportWitness, pushforward]
  rw [← Equiv.sum_comp (srcPermEquiv G H φ hind t π)
    (fun p => if extAssign G H φ hind t p = gRelabel π ω then
      transportSource G H φ t ΔH p else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hν : transportSource G H φ t ΔH (srcPermEquiv G H φ hind t π p)
      = transportSource G H φ t ΔH p := by
    change ΔH (gRelabel (fun f : H.Edge => π (edgeMap G H φ hind f)) p.1)
        * unifLaw (OutObs G H φ t) _ = ΔH p.1 * unifLaw (OutObs G H φ t) p.2
    rw [hsym]
    rfl
  have hc : (extAssign G H φ hind t (srcPermEquiv G H φ hind t π p) = gRelabel π ω)
      ↔ (extAssign G H φ hind t p = ω) := by
    rw [extAssign_relabel G H φ hφ hind t π p]
    exact ⟨fun h => gRelabel_injective π h, fun h => by rw [h]⟩
  rw [if_congr hc rfl rfl, hν]



/-! ## Splitting an outcome of `G` into its `H`-part and its outside part -/

/-- The outcome of `G` assembled from an `H`-outcome and an outside outcome. -/
noncomputable def mergeVert (G H : PairGraph) (φ : H.V → G.V)
    (q : (H.V → Bool) × (OutVert G H φ → Bool)) : G.V → Bool := fun v =>
  if h : InRange G H φ v then q.1 h.choose else q.2 ⟨v, h⟩

theorem mergeVert_in (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (q : (H.V → Bool) × (OutVert G H φ → Bool)) (u : H.V) :
    mergeVert G H φ q (φ u) = q.1 u := by
  have hr : InRange G H φ (φ u) := ⟨u, rfl⟩
  rw [mergeVert, dite_eq_left hr]
  exact congrArg q.1 (hφ hr.choose_spec)

theorem mergeVert_out (G H : PairGraph) (φ : H.V → G.V)
    (q : (H.V → Bool) × (OutVert G H φ → Bool)) (v : G.V) (h : ¬ InRange G H φ v) :
    mergeVert G H φ q v = q.2 ⟨v, h⟩ := by
  rw [mergeVert, dite_eq_right h]

/-- Outcomes of `G` split as an `H`-outcome together with an outcome on the outside vertices. -/
noncomputable def vertEquiv (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ) :
    ((H.V → Bool) × (OutVert G H φ → Bool)) ≃ (G.V → Bool) where
  toFun := mergeVert G H φ
  invFun w := (fun u => w (φ u), fun v => w v.1)
  left_inv q := by
    refine Prod.ext ?_ ?_
    · funext u; exact mergeVert_in G H φ hφ q u
    · funext v; exact mergeVert_out G H φ q v.1 v.2
  right_inv w := by
    funext v
    by_cases h : InRange G H φ v
    · obtain ⟨u, rfl⟩ := h
      exact mergeVert_in G H φ hφ _ u
    · exact mergeVert_out G H φ _ v h


/-! ## The two parts of an injectable set -/

theorem copyObs_fst {Γ : PairGraph} {t : ℕ} (ι : Γ.Edge → Fin t) (v : Γ.V) :
    (copyObs ι v).1 = v := rfl

theorem mem_copySet_self {Γ : PairGraph} {t : ℕ} (ι : Γ.Edge → Fin t) (o : GObs Γ t)
    (h : o ∈ copySet ι) : o = copyObs ι o.1 := by
  simp only [copySet, Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨v, hv⟩ := h
  subst hv
  rfl

theorem extAssign_copy_in (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ) (ι : G.Edge → Fin t)
    (p : GAssign H t × (OutObs G H φ t → Bool)) (u : H.V) :
    extAssign G H φ hind t p (copyObs ι (φ u))
      = p.1 (copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u) := by
  rw [extAssign_in G H φ hφ hind t p _ u rfl]
  rfl

/-- The `H`-part of an injectable set of copied observations of `G`. -/
def injPart (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) : Finset (GObs H t) :=
  (Finset.univ.filter (fun u : H.V => copyObs ι (φ u) ∈ S)).image
    (copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)))

/-- The outside part of a set of copied observations of `G`. -/
def outPart (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) (S : Finset (GObs G t)) :
    Finset (OutObs G H φ t) := Finset.univ.filter (fun x => x.1 ∈ S)

/-- The outside vertices read by an injectable set of copied observations of `G`. -/
def outVertPart (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) (S : Finset (GObs G t))
    (ι : G.Edge → Fin t) : Finset (OutVert G H φ) :=
  Finset.univ.filter (fun v => copyObs ι v.1 ∈ S)

/-- The outcome pattern that the `H`-part inherits. -/
def readInjPart (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) (ψ : S → Bool) :
    (injPart G H φ hind t S ι) → Bool :=
  fun y => if h : copyObs ι (φ y.1.1) ∈ S then ψ ⟨copyObs ι (φ y.1.1), h⟩ else false

/-- The outcome pattern that the outside part inherits. -/
def readOutPart (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) (S : Finset (GObs G t))
    (ψ : S → Bool) : (outPart G H φ t S) → Bool :=
  fun x => if h : x.1.1 ∈ S then ψ ⟨x.1.1, h⟩ else false

/-- The outcome pattern that the outside vertices inherit. -/
def readOutVertPart (G H : PairGraph) (φ : H.V → G.V) (t : ℕ) (S : Finset (GObs G t))
    (ι : G.Edge → Fin t) (ψ : S → Bool) : (outVertPart G H φ t S ι) → Bool :=
  fun x => if h : copyObs ι x.1.1 ∈ S then ψ ⟨copyObs ι x.1.1, h⟩ else false

theorem readInjPart_apply (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) (ψ : S → Bool)
    (u : H.V) (hu : copyObs ι (φ u) ∈ S)
    (hy : copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u ∈ injPart G H φ hind t S ι) :
    readInjPart G H φ hind t S ι ψ ⟨_, hy⟩ = ψ ⟨copyObs ι (φ u), hu⟩ := by
  change (if h : copyObs ι (φ u) ∈ S then ψ ⟨copyObs ι (φ u), h⟩ else false) = _
  rw [dite_eq_left hu]

theorem injPart_injectable (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) :
    GInjectable (injPart G H φ hind t S ι) := by
  refine ⟨fun f : H.Edge => ι (edgeMap G H φ hind f), ?_⟩
  intro y hy
  simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨u, -, rfl⟩ := hy
  exact Finset.mem_image_of_mem _ (Finset.mem_univ u)

theorem card_outPart_eq (G H : PairGraph) (φ : H.V → G.V) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) (hS : S ⊆ copySet ι) :
    (outPart G H φ t S).card = (outVertPart G H φ t S ι).card := by
  refine Finset.card_bij (fun (x : OutObs G H φ t) (_ : x ∈ outPart G H φ t S) =>
    (⟨x.1.1, x.2⟩ : OutVert G H φ)) ?_ ?_ ?_
  · intro x hx
    have hmem : x.1 ∈ S := (Finset.mem_filter.1 hx).2
    simp only [outVertPart, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← mem_copySet_self ι x.1 (hS hmem)]
    exact hmem
  · intro x hx y hy hxy
    have hmx : x.1 ∈ S := (Finset.mem_filter.1 hx).2
    have hmy : y.1 ∈ S := (Finset.mem_filter.1 hy).2
    have hv : x.1.1 = y.1.1 := congrArg Subtype.val hxy
    apply Subtype.ext
    rw [mem_copySet_self ι x.1 (hS hmx), mem_copySet_self ι y.1 (hS hmy), hv]
  · intro v hv
    have hmem : copyObs ι v.1 ∈ S := (Finset.mem_filter.1 hv).2
    refine ⟨⟨copyObs ι v.1, v.2⟩, ?_, rfl⟩
    simp only [outPart, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem

theorem gRestrict_extAssign_iff (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) (hS : S ⊆ copySet ι) (ψ : S → Bool)
    (p : GAssign H t × (OutObs G H φ t → Bool)) :
    (gRestrict S (extAssign G H φ hind t p) = ψ) ↔
      (gRestrict (injPart G H φ hind t S ι) p.1 = readInjPart G H φ hind t S ι ψ
        ∧ (fun x : (outPart G H φ t S) => p.2 x.1) = readOutPart G H φ t S ψ) := by
  constructor
  · intro h
    constructor
    · funext y
      obtain ⟨y, hy⟩ := y
      simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      have hval : extAssign G H φ hind t p (copyObs ι (φ u)) = ψ ⟨copyObs ι (φ u), hu⟩ :=
        congrFun h ⟨copyObs ι (φ u), hu⟩
      rw [extAssign_copy_in G H φ hφ hind t ι p u] at hval
      change p.1 (copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u) = _
      rw [readInjPart_apply G H φ hind t S ι ψ u hu]
      exact hval
    · funext x
      obtain ⟨x, hx⟩ := x
      have hmem : x.1 ∈ S := (Finset.mem_filter.1 hx).2
      have hval : extAssign G H φ hind t p x.1 = ψ ⟨x.1, hmem⟩ := congrFun h ⟨x.1, hmem⟩
      rw [extAssign_out G H φ hind t p x.1 x.2] at hval
      change p.2 x = _
      simp only [readOutPart]
      rw [dite_eq_left hmem]
      exact hval
  · rintro ⟨h1, h2⟩
    funext o
    obtain ⟨o, ho⟩ := o
    have hoc : o = copyObs ι o.1 := mem_copySet_self ι o (hS ho)
    change extAssign G H φ hind t p o = ψ ⟨o, ho⟩
    by_cases hr : InRange G H φ o.1
    · obtain ⟨u, hu⟩ := hr
      have hou : o = copyObs ι (φ u) := by rw [hu]; exact hoc
      have hmemu : copyObs ι (φ u) ∈ S := by rw [← hou]; exact ho
      have hy : copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u
          ∈ injPart G H φ hind t S ι := by
        simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, hmemu, rfl⟩
      have h1' : p.1 (copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u)
          = ψ ⟨copyObs ι (φ u), hmemu⟩ := by
        have hc := congrFun h1 (⟨_, hy⟩ : injPart G H φ hind t S ι)
        rwa [readInjPart_apply G H φ hind t S ι ψ u hmemu] at hc
      have step1 : extAssign G H φ hind t p o
          = p.1 (copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u) := by
        rw [hou]; exact extAssign_copy_in G H φ hφ hind t ι p u
      rw [step1, h1']
      exact congrArg ψ (Subtype.ext hou.symm)
    · have hxmem : (⟨o, hr⟩ : OutObs G H φ t) ∈ outPart G H φ t S := by
        simp only [outPart, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ho
      have h2' : p.2 ⟨o, hr⟩ = readOutPart G H φ t S ψ ⟨⟨o, hr⟩, hxmem⟩ :=
        congrFun h2 ⟨⟨o, hr⟩, hxmem⟩
      simp only [readOutPart] at h2'
      rw [dite_eq_left ho] at h2'
      rw [extAssign_out G H φ hind t p o hr]
      exact h2'

theorem gPartyRead_mergeVert_iff (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S : Finset (GObs G t)) (ι : G.Edge → Fin t) (hS : S ⊆ copySet ι) (ψ : S → Bool)
    (q : (H.V → Bool) × (OutVert G H φ → Bool)) :
    (gPartyRead S (mergeVert G H φ q) = ψ) ↔
      (gPartyRead (injPart G H φ hind t S ι) q.1 = readInjPart G H φ hind t S ι ψ
        ∧ (fun x : (outVertPart G H φ t S ι) => q.2 x.1)
            = readOutVertPart G H φ t S ι ψ) := by
  constructor
  · intro h
    constructor
    · funext y
      obtain ⟨y, hy⟩ := y
      simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      have hval : mergeVert G H φ q (φ u) = ψ ⟨copyObs ι (φ u), hu⟩ :=
        congrFun h ⟨copyObs ι (φ u), hu⟩
      rw [mergeVert_in G H φ hφ q u] at hval
      change q.1 u = _
      rw [readInjPart_apply G H φ hind t S ι ψ u hu]
      exact hval
    · funext x
      obtain ⟨x, hx⟩ := x
      have hmem : copyObs ι x.1 ∈ S := (Finset.mem_filter.1 hx).2
      have hval : mergeVert G H φ q x.1 = ψ ⟨copyObs ι x.1, hmem⟩ :=
        congrFun h ⟨copyObs ι x.1, hmem⟩
      rw [mergeVert_out G H φ q x.1 x.2] at hval
      change q.2 x = _
      simp only [readOutVertPart]
      rw [dite_eq_left hmem]
      exact hval
  · rintro ⟨h1, h2⟩
    funext o
    obtain ⟨o, ho⟩ := o
    have hoc : o = copyObs ι o.1 := mem_copySet_self ι o (hS ho)
    change mergeVert G H φ q o.1 = ψ ⟨o, ho⟩
    by_cases hr : InRange G H φ o.1
    · obtain ⟨u, hu⟩ := hr
      have hou : o = copyObs ι (φ u) := by rw [hu]; exact hoc
      have hmemu : copyObs ι (φ u) ∈ S := by rw [← hou]; exact ho
      have hy : copyObs (fun f : H.Edge => ι (edgeMap G H φ hind f)) u
          ∈ injPart G H φ hind t S ι := by
        simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, hmemu, rfl⟩
      have h1' : q.1 u = ψ ⟨copyObs ι (φ u), hmemu⟩ := by
        have hc := congrFun h1 (⟨_, hy⟩ : injPart G H φ hind t S ι)
        rwa [readInjPart_apply G H φ hind t S ι ψ u hmemu] at hc
      rw [← hu, mergeVert_in G H φ hφ q u, h1']
      exact congrArg ψ (Subtype.ext hou.symm)
    · have hxmem : (⟨o.1, hr⟩ : OutVert G H φ) ∈ outVertPart G H φ t S ι := by
        simp only [outVertPart, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hoc]
        exact ho
      have h2' : q.2 ⟨o.1, hr⟩ = readOutVertPart G H φ t S ι ψ ⟨⟨o.1, hr⟩, hxmem⟩ :=
        congrFun h2 ⟨⟨o.1, hr⟩, hxmem⟩
      simp only [readOutVertPart] at h2'
      rw [dite_eq_left (by rw [← hoc]; exact ho : copyObs ι o.1 ∈ S)] at h2'
      rw [mergeVert_out G H φ q o.1 hr, h2']
      exact congrArg ψ (Subtype.ext hoc.symm)


/-- The marginal of the transported target on an injectable set factorizes into the marginal
of `P` on the `H`-part and fair bits on the outside vertices it reads. -/
theorem transportTarget_partyRead_split (G H : PairGraph) (φ : H.V → G.V)
    (hφ : Function.Injective φ) (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v))
    (t : ℕ) (P : GTarget H) (S : Finset (GObs G t)) (ι : G.Edge → Fin t)
    (hS : S ⊆ copySet ι) (ψ : S → Bool) :
    pushforward (transportTarget G H φ P) (gPartyRead S) ψ
      = pushforward P (gPartyRead (injPart G H φ hind t S ι))
          (readInjPart G H φ hind t S ι ψ)
        * (1 / 2 : ℝ) ^ (outVertPart G H φ t S ι).card := by
  have hR : pushforward (transportTarget G H φ P) (gPartyRead S) ψ
      = pushforward P (gPartyRead (injPart G H φ hind t S ι))
          (readInjPart G H φ hind t S ι ψ)
        * unifLaw (outVertPart G H φ t S ι) (readOutVertPart G H φ t S ι ψ) := by
    rw [← unifLaw_restrict (A := OutVert G H φ) (fun x : (outVertPart G H φ t S ι) => x.1)
      Subtype.coe_injective, ← pushforward_prod_apply]
    simp only [pushforward]
    rw [← Equiv.sum_comp (vertEquiv G H φ hφ)
      (fun w => if gPartyRead S w = ψ then transportTarget G H φ P w else 0)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hveq : (vertEquiv G H φ hφ) q = mergeVert G H φ q := rfl
    rw [hveq]
    have hval : transportTarget G H φ P (mergeVert G H φ q)
        = P q.1 * unifLaw (OutVert G H φ) q.2 := by
      simp only [transportTarget, unifLaw, card_outVert G H φ hφ]
      congr 1
      exact congrArg P (funext fun u => mergeVert_in G H φ hφ q u)
    rw [hval]
    exact if_congr (gPartyRead_mergeVert_iff G H φ hφ hind t S ι hS ψ q) rfl rfl
  rw [hR]
  simp only [unifLaw, Fintype.card_coe]


/-! ## Ancestry -/

theorem mem_gAncestors_copyObs {Γ : PairGraph} {t : ℕ} (ι : Γ.Edge → Fin t) (v : Γ.V)
    (e : Γ.Edge) (he : e ∈ Γ.inc v) : (e, ι e) ∈ gAncestors (copyObs ι v) := by
  simp only [gAncestors, Finset.mem_image]
  exact ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩

theorem gAncestors_copyObs_mem {Γ : PairGraph} {t : ℕ} (ι : Γ.Edge → Fin t) (v : Γ.V)
    (z : GLatent Γ t) (hz : z ∈ gAncestors (copyObs ι v)) : z.1 ∈ Γ.inc v ∧ z.2 = ι z.1 := by
  simp only [gAncestors, Finset.mem_image] at hz
  obtain ⟨e, -, rfl⟩ := hz
  exact ⟨e.2, rfl⟩

/-- Ancestrally independent sets are disjoint: no copied observation is parentless. -/
theorem ai_disjoint {Γ : PairGraph} {t : ℕ} (S T : Finset (GObs Γ t))
    (h : GAncestrallyIndependent S T) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro o hoS hoT
  obtain ⟨e, he⟩ := inc_nonempty Γ o.1
  have hz : (e, o.2 ⟨e, he⟩) ∈ gAncestors o := by
    simp only [gAncestors, Finset.mem_image]
    exact ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩
  exact (Finset.disjoint_left.1 h (Finset.mem_biUnion.2 ⟨o, hoS, hz⟩))
    (Finset.mem_biUnion.2 ⟨o, hoT, hz⟩)

/-- Ancestral independence in `G` is inherited by the `H`-parts. -/
theorem injPart_ai (G H : PairGraph) (φ : H.V → G.V)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (t : ℕ)
    (S T : Finset (GObs G t)) (ιS ιT : G.Edge → Fin t) (h : GAncestrallyIndependent S T) :
    GAncestrallyIndependent (injPart G H φ hind t S ιS) (injPart G H φ hind t T ιT) := by
  rw [GAncestrallyIndependent, Finset.disjoint_left]
  intro z hzS hzT
  obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 hzS
  simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  obtain ⟨hz1, hz2⟩ := gAncestors_copyObs_mem _ u z hzy
  obtain ⟨y', hy', hzy'⟩ := Finset.mem_biUnion.1 hzT
  simp only [injPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
  obtain ⟨u', hu', rfl⟩ := hy'
  obtain ⟨hz1', hz2'⟩ := gAncestors_copyObs_mem _ u' z hzy'
  have hwS : (edgeMap G H φ hind z.1, z.2) ∈ gAncestorsOf S := by
    refine Finset.mem_biUnion.2 ⟨copyObs ιS (φ u), hu, ?_⟩
    rw [hz2]
    exact mem_gAncestors_copyObs ιS (φ u) _ (edgeMap_mem_inc G H φ hind u z.1 hz1)
  have hwT : (edgeMap G H φ hind z.1, z.2) ∈ gAncestorsOf T := by
    refine Finset.mem_biUnion.2 ⟨copyObs ιT (φ u'), hu', ?_⟩
    rw [hz2']
    exact mem_gAncestors_copyObs ιT (φ u') _ (edgeMap_mem_inc G H φ hind u' z.1 hz1')
  exact (Finset.disjoint_left.1 h hwS) hwT

/-- Independent fair bits restricted along a family of injections indexed by a sigma type. -/
theorem unifLaw_restrictPi {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    {β : Fin n → Type*} [∀ m, Fintype (β m)] [∀ m, DecidableEq (β m)]
    (ρ : (Σ m : Fin n, β m) → A) (hρ : Function.Injective ρ) (η : ∀ m, β m → Bool) :
    pushforward (unifLaw A) (fun ξ => fun (m : Fin n) (b : β m) => ξ (ρ ⟨m, b⟩)) η
      = (1 / 2 : ℝ) ^ (∑ m : Fin n, Fintype.card (β m)) := by
  have h1 : ∀ ξ : A → Bool, ((fun (m : Fin n) (b : β m) => ξ (ρ ⟨m, b⟩)) = η)
      ↔ ((fun x => ξ (ρ x)) = fun x : (Σ m : Fin n, β m) => η x.1 x.2) := by
    intro ξ
    constructor
    · intro h; funext x; obtain ⟨m, b⟩ := x; exact congrFun (congrFun h m) b
    · intro h; funext m b; exact congrFun h ⟨m, b⟩
  have h2 : pushforward (unifLaw A) (fun ξ => fun x : (Σ m : Fin n, β m) => ξ (ρ x))
      (fun x => η x.1 x.2) = unifLaw (Σ m : Fin n, β m) (fun x => η x.1 x.2) :=
    congrFun (unifLaw_restrict ρ hρ) _
  simp only [pushforward] at h2 ⊢
  rw [Finset.sum_congr rfl (fun ξ _ => if_congr (h1 ξ) rfl rfl), h2]
  simp only [unifLaw, Fintype.card_sigma]

/-! ## Injectable marginals and ancestral products -/

/-- Every `G`-injectable set carries the corresponding marginal of the transported target. -/
theorem transport_injectableMarginals (G H : PairGraph) (φ : H.V → G.V)
    (hφ : Function.Injective φ) (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v))
    (t : ℕ) (P : GTarget H) (ΔH : GAssign H t → ℝ) (hinj : GInjectableMarginals t ΔH P) :
    GInjectableMarginals t (transportWitness G H φ hind t ΔH) (transportTarget G H φ P) := by
  intro S hSinj
  obtain ⟨ι, hS⟩ := hSinj
  simp only [transportWitness, pushforward_comp]
  funext ψ
  have hL : pushforward (transportSource G H φ t ΔH)
        (gRestrict S ∘ extAssign G H φ hind t) ψ
      = pushforward ΔH (gRestrict (injPart G H φ hind t S ι))
          (readInjPart G H φ hind t S ι ψ)
        * unifLaw (outPart G H φ t S) (readOutPart G H φ t S ψ) := by
    rw [← unifLaw_restrict (A := OutObs G H φ t) (fun x : (outPart G H φ t S) => x.1)
      Subtype.coe_injective, ← pushforward_prod_apply]
    simp only [pushforward, Function.comp_apply, transportSource]
    exact Finset.sum_congr rfl fun p _ =>
      if_congr (gRestrict_extAssign_iff G H φ hφ hind t S ι hS ψ p) rfl rfl
  have hR := transportTarget_partyRead_split G H φ hφ hind t P S ι hS ψ
  rw [hL, hR, congrFun (hinj (injPart G H φ hind t S ι) (injPart_injectable G H φ hind t S ι))
    (readInjPart G H φ hind t S ι ψ)]
  simp only [unifLaw, Fintype.card_coe, card_outPart_eq G H φ t S ι hS]

/-- Every finite family of pairwise ancestrally independent `G`-injectable sets carries the
product of the corresponding marginals of the transported target. -/
theorem transport_ancestralProducts (G H : PairGraph) (φ : H.V → G.V)
    (hφ : Function.Injective φ) (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v))
    (t : ℕ) (P : GTarget H) (ΔH : GAssign H t → ℝ) (hprod : GAncestralProducts t ΔH P) :
    GAncestralProducts t (transportWitness G H φ hind t ΔH) (transportTarget G H φ P) := by
  intro n S hInj hAIfam
  choose ι hι using hInj
  simp only [transportWitness, pushforward_comp]
  funext ψ
  have hinjH : ∀ m, GInjectable (injPart G H φ hind t (S m) (ι m)) :=
    fun m => injPart_injectable G H φ hind t (S m) (ι m)
  have haiH : ∀ m m', m ≠ m' → GAncestrallyIndependent
      (injPart G H φ hind t (S m) (ι m)) (injPart G H φ hind t (S m') (ι m')) :=
    fun m m' hmm => injPart_ai G H φ hind t (S m) (S m') (ι m) (ι m') (hAIfam m m' hmm)
  have hρinj : Function.Injective
      (fun x : (Σ m : Fin n, (outPart G H φ t (S m))) => x.2.1) := by
    rintro ⟨m, x, hx⟩ ⟨m', x', hx'⟩ hxx
    have hxx' : x = x' := hxx
    have hm : m = m' := by
      by_contra hne
      have h1 : x.1 ∈ S m := (Finset.mem_filter.1 hx).2
      have h2 : x.1 ∈ S m' := by rw [hxx']; exact (Finset.mem_filter.1 hx').2
      exact (Finset.disjoint_left.1 (ai_disjoint (S m) (S m') (hAIfam m m' hne)) h1) h2
    subst hm
    subst hxx'
    rfl
  have hunif : pushforward (unifLaw (OutObs G H φ t))
      (fun ξ => fun (m : Fin n) (b : (outPart G H φ t (S m))) => ξ b.1)
      (fun m => readOutPart G H φ t (S m) (ψ m))
      = (1 / 2 : ℝ) ^ (∑ m : Fin n, Fintype.card ((outPart G H φ t (S m)))) :=
    unifLaw_restrictPi (fun x : (Σ m : Fin n, (outPart G H φ t (S m))) => x.2.1) hρinj _
  have hL : pushforward (transportSource G H φ t ΔH)
        ((fun ω m => gRestrict (S m) ω) ∘ extAssign G H φ hind t) ψ
      = pushforward ΔH (fun ω m => gRestrict (injPart G H φ hind t (S m) (ι m)) ω)
          (fun m => readInjPart G H φ hind t (S m) (ι m) (ψ m))
        * pushforward (unifLaw (OutObs G H φ t))
            (fun ξ => fun (m : Fin n) (b : (outPart G H φ t (S m))) => ξ b.1)
            (fun m => readOutPart G H φ t (S m) (ψ m)) := by
    rw [← pushforward_prod_apply]
    simp only [pushforward, Function.comp_apply, transportSource]
    refine Finset.sum_congr rfl fun p _ => if_congr ?_ rfl rfl
    constructor
    · intro h
      refine ⟨funext fun m => ?_, funext fun m => ?_⟩
      · exact ((gRestrict_extAssign_iff G H φ hφ hind t (S m) (ι m) (hι m) (ψ m) p).1
          (congrFun h m)).1
      · exact ((gRestrict_extAssign_iff G H φ hφ hind t (S m) (ι m) (hι m) (ψ m) p).1
          (congrFun h m)).2
    · rintro ⟨h1, h2⟩
      funext m
      exact (gRestrict_extAssign_iff G H φ hφ hind t (S m) (ι m) (hι m) (ψ m) p).2
        ⟨congrFun h1 m, congrFun h2 m⟩
  have hcards : (∑ m : Fin n, Fintype.card ((outPart G H φ t (S m))))
      = ∑ m : Fin n, (outVertPart G H φ t (S m) (ι m)).card :=
    Finset.sum_congr rfl fun m _ => by
      rw [Fintype.card_coe]; exact card_outPart_eq G H φ t (S m) (ι m) (hι m)
  rw [hL, congrFun (hprod n (fun m => injPart G H φ hind t (S m) (ι m)) hinjH haiH) _, hunif,
    hcards, Finset.prod_congr rfl (fun m _ =>
      transportTarget_partyRead_split G H φ hφ hind t P (S m) (ι m) (hι m) (ψ m)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end TransportFeasible

open TransportFeasible

end Transport

open Transport Transport.TransportFeasible in
/-- Transport of a witness (AUDIT-NOTES A6, forward half; paper `lem:transport`(ii)). An
`H`-witness extends to a `G`-witness: a copied observation at an `H`-vertex ignores the copy
indices of the edges leaving `H`, and every copied observation at an outside vertex gets its own
independent fair bit. -/
theorem transport_ai_feasible (G H : PairGraph) (φ : H.V → G.V)
    (hφ : Function.Injective φ) (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v))
    (t : ℕ) (P : GTarget H) (hAI : GAIFeasible H t P) :
    GAIFeasible G t (transportTarget G H φ P) := by
  obtain ⟨ΔH, hlaw, hsym, hdiag, hinj, hprod⟩ := hAI
  exact ⟨transportWitness G H φ hind t ΔH, transportWitness_isLaw G H φ hind t hlaw,
    transport_symmetric G H φ hφ hind t ΔH hsym,
    transport_diag G H φ hφ hind t P ΔH hdiag,
    transport_injectableMarginals G H φ hφ hind t P ΔH hinj,
    transport_ancestralProducts G H φ hφ hind t P ΔH hprod⟩

open Transport in
/-- Restriction of a model (AUDIT-NOTES A6, backward half; paper `lem:transport`(i)). A
`G`-model for `P ⊗ fair` restricts to an `H`-model for `P`: by inducedness a source of `G`
outside the image of `H` is read by at most one `H`-vertex, so it can be averaged out locally as
private randomness at that vertex, and the fair bits outside integrate to one. -/
theorem transport_compatible_restrict (G H : PairGraph) (φ : H.V → G.V)
    (hφ : Function.Injective φ) (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v))
    (P : GTarget H) (hc : GCompatible G (transportTarget G H φ P)) : GCompatible H P := by
  obtain ⟨M, hM, hlaw⟩ := hc
  exact ⟨restrictModel G H φ hφ hind M, restrictModel_valid G H φ hφ hind M hM,
    restrictModel_law G H φ hφ hind P M hM hlaw⟩

/-- AUDIT-NOTES A6, induced-subgraph transport. If `H` embeds in `G` as an induced connected
subgraph and `P` is an `H`-target that passes the order-`t` AI test but is incompatible, then
`P` tensored with fair bits on the remaining vertices of `G` passes the order-`t` AI test for
`G` and is incompatible for `G`. Forward: a `G`-model restricted to `V(H)` is an `H`-model,
since a crossing source reaches only one `H`-vertex and can be absorbed as private
randomness, and inducedness means there are no extra internal sources. Backward: extend the
`H`-witness by ignoring crossing-edge indices at `H`-vertices and giving independent fair
bits to the outside observations. -/
theorem induced_transport (G H : PairGraph) (φ : H.V → G.V) (hφ : Function.Injective φ)
    (hind : ∀ u v : H.V, H.G.Adj u v ↔ G.G.Adj (φ u) (φ v)) (hconn : H.G.Connected)
    (t : ℕ) (P : GTarget H) (hAI : GAIFeasible H t P) (hinc : ¬ GCompatible H P) :
    GAIFeasible G t (transportTarget G H φ P) ∧ ¬ GCompatible G (transportTarget G H φ P) := by
  -- Connectivity of `H` is not needed for either half.
  let _ := hconn
  exact ⟨transport_ai_feasible G H φ hφ hind t P hAI,
    fun hc => hinc (transport_compatible_restrict G H φ hφ hind P hc)⟩

/-! ### Exhaustion: the two induced subgraphs

The graph theory behind `exhaustion`. Everything in this section is about a bare `SimpleGraph`;
`PairGraph` plays no role until the theorem itself. -/

namespace Exhaustion

open SimpleGraph

/-- Unfolding lemma for the cycle graph's adjacency. -/
private theorem cycleAdj_adj_iff (m : ℕ) (a b : Fin m) :
    (cycleAdj m).Adj a b ↔ a ≠ b ∧ ((a.val + 1) % m = b.val ∨ (b.val + 1) % m = a.val) :=
  Iff.rfl

/-- The arc of a cycle between indices `n < k ≤ length - 1` is a path of length `k - n`. -/
private theorem arc_isPath {V : Type} {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (hw : w.IsCycle) {n k : ℕ} (hnk : n < k) (hk : k < w.length) :
    ∃ p : G.Walk (w.getVert n) (w.getVert k), p.IsPath ∧ p.length = k - n := by
  have hend : (w.drop n).getVert (k - n) = w.getVert k := by
    rw [SimpleGraph.Walk.drop_getVert]
    congr 1
    omega
  have hlen : ((w.drop n).take (k - n)).length = k - n := by
    simp only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
    omega
  have hp0 : ((w.drop n).take (k - n)).IsPath := by
    rw [← SimpleGraph.Walk.IsPath.getVert_injOn_iff]
    intro c hc d hd hcd
    simp only [Set.mem_ofPred_eq, hlen] at hc hd
    rw [SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.take_getVert,
      SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.drop_getVert] at hcd
    have e1 : (k - n) ⊓ c = c := by omega
    have e2 : (k - n) ⊓ d = d := by omega
    rw [e1, e2] at hcd
    have := hw.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hcd
    omega
  refine ⟨((w.drop n).take (k - n)).copy rfl hend, ?_, ?_⟩
  · rwa [SimpleGraph.Walk.isPath_copy]
  · rwa [SimpleGraph.Walk.length_copy]

theorem induced_cycle_of_not_acyclic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hnac : ¬ G.IsAcyclic) :
    ∃ (m : ℕ) (_ : 3 ≤ m) (ψ : Fin m → V), Function.Injective ψ ∧
      ∀ a b : Fin m, (cycleAdj m).Adj a b ↔ G.Adj (ψ a) (ψ b) := by
  classical
  -- a cycle exists
  obtain ⟨v₀, c₀, hc₀⟩ : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
    by_contra hcon
    exact hnac fun v c hc => hcon ⟨v, c, hc⟩
  -- a cycle of minimum length exists
  have hex : ∃ n : ℕ, ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ c.length = n :=
    ⟨c₀.length, v₀, c₀, hc₀, rfl⟩
  obtain ⟨a, w, hw, hwlen⟩ := Nat.find_spec hex
  have hmin : ∀ (x : V) (c : G.Walk x x), c.IsCycle → w.length ≤ c.length := by
    intro x c hc
    rw [hwlen]
    exact Nat.find_le ⟨x, c, hc, rfl⟩
  have hm3 : 3 ≤ w.length := hw.three_le_length
  -- a minimum-length cycle has no chord
  have key : ∀ n k : ℕ, n < k → k < w.length →
      G.Adj (w.getVert n) (w.getVert k) → (k = n + 1 ∨ (n = 0 ∧ k = w.length - 1)) := by
    intro n k hnk hk hadj
    by_contra hcon
    have h1 : k ≠ n + 1 := fun h => hcon (Or.inl h)
    have h2 : ¬ (n = 0 ∧ k = w.length - 1) := fun h => hcon (Or.inr h)
    obtain ⟨p, hp, hplen⟩ := arc_isPath hw hnk hk
    have hne : s(w.getVert k, w.getVert n) ∉ p.edges := by
      intro hmem
      rw [Sym2.eq_swap] at hmem
      have := hp.length_eq_one_of_mem_edges hmem
      omega
    have hcyc : (SimpleGraph.Walk.cons hadj.symm p).IsCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff p hadj.symm).mpr ⟨hp, hne⟩
    have hle := hmin _ _ hcyc
    rw [SimpleGraph.Walk.length_cons, hplen] at hle
    omega
  refine ⟨w.length, hm3, fun i => w.getVert i.val, ?_, ?_⟩
  · intro i j hij
    have := hw.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
    exact Fin.ext this
  · intro i j
    rw [cycleAdj_adj_iff]
    constructor
    · rintro ⟨hne, hcase⟩
      have fwd : ∀ c d : Fin w.length, (c.val + 1) % w.length = d.val →
          G.Adj (w.getVert c.val) (w.getVert d.val) := by
        intro c d hcd
        have hc : c.val < w.length := c.isLt
        by_cases h : c.val + 1 = w.length
        · have hd : d.val = 0 := by rw [← hcd, h, Nat.mod_self]
          have hadj := w.adj_getVert_succ hc
          rw [h] at hadj
          rw [hd]
          simpa [SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero] using hadj
        · have hd : d.val = c.val + 1 := by
            rw [← hcd, Nat.mod_eq_of_lt (by omega)]
          rw [hd]
          exact w.adj_getVert_succ hc
      rcases hcase with h | h
      · exact fwd i j h
      · exact (fwd j i h).symm
    · intro hadj
      have hne : i ≠ j := by
        rintro rfl
        exact hadj.ne rfl
      refine ⟨hne, ?_⟩
      have hij : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_ge i.val j.val with h | h
      · rcases key i.val j.val h j.isLt hadj with h' | ⟨h1, h2⟩
        · left; rw [h', Nat.mod_eq_of_lt (by omega)]
        · right
          rw [h2, show w.length - 1 + 1 = w.length by omega, Nat.mod_self, h1]
      · have h' : j.val < i.val := by omega
        rcases key j.val i.val h' i.isLt hadj.symm with h'' | ⟨h1, h2⟩
        · right; rw [h'', Nat.mod_eq_of_lt (by omega)]
        · left
          rw [h2, show w.length - 1 + 1 = w.length by omega, Nat.mod_self, h1]

/-- Subwalks of a shortest walk are shortest: for a walk `p` from `u` to `v` whose length
realizes `G.dist u v`, and `i ≤ j ≤ p.length`, the distance between the `i`-th and `j`-th
vertices of `p` is exactly `j - i`. -/
theorem dist_getVert_of_shortest {V : Type} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hend : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  set w : G.Walk (p.getVert i) (p.getVert j) :=
    ((p.drop i).take (j - i)).copy rfl hend with hw
  have hwlen : w.length = j - i := by
    rw [hw, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  refine le_antisymm (hwlen ▸ SimpleGraph.dist_le w) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hreach : G.Reachable (p.getVert i) (p.getVert j) := ⟨w⟩
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hqlt : q.length < j - i := hq ▸ hlt
  have hr := SimpleGraph.dist_le ((p.take i).append (q.append (p.drop j)))
  rw [Walk.length_append, Walk.length_append, Walk.take_length, Walk.drop_length] at hr
  omega

/-- Symmetric form of `dist_getVert_of_shortest`. -/
theorem dist_getVert_of_shortest' {V : Type} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = max i j - min i j := by
  rcases le_total i j with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact dist_getVert_of_shortest G p hp h hj
  · rw [max_eq_left h, min_eq_right h, SimpleGraph.dist_comm]
    exact dist_getVert_of_shortest G p hp h hi

theorem induced_path5_of_dist {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (hd : 4 ≤ G.dist u v) :
    ∃ ψ : Fin 5 → V, Function.Injective ψ ∧
      ∀ a b : Fin 5, (pathAdj 5).Adj a b ↔ G.Adj (ψ a) (ψ b) := by
  -- `4 ≤ dist` forces reachability.
  have hreach : G.Reachable u v := by
    by_contra hnr
    have : G.dist u v = 0 := SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hnr)
    omega
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hlen : 4 ≤ p.length := by omega
  refine ⟨fun i => p.getVert i.val, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hval : a.val ≠ b.val := fun h => hne (Fin.ext h)
    have ha : a.val ≤ p.length := le_trans (Nat.le_of_lt_succ a.isLt) hlen
    have hb : b.val ≤ p.length := le_trans (Nat.le_of_lt_succ b.isLt) hlen
    have hab' : p.getVert a.val = p.getVert b.val := hab
    have hdd := dist_getVert_of_shortest' G p hp ha hb
    rw [hab', SimpleGraph.dist_self] at hdd
    rcases le_total a.val b.val with h | h
    · rw [max_eq_right h, min_eq_left h] at hdd; omega
    · rw [max_eq_left h, min_eq_right h] at hdd; omega
  · intro a b
    have ha : a.val ≤ p.length := le_trans (Nat.le_of_lt_succ a.isLt) hlen
    have hb : b.val ≤ p.length := le_trans (Nat.le_of_lt_succ b.isLt) hlen
    have hpa : (pathAdj 5).Adj a b ↔ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := Iff.rfl
    rw [hpa]
    constructor
    · rintro (h | h)
      · have hlt : a.val < p.length := by omega
        have := p.adj_getVert_succ hlt
        rwa [h] at this
      · have hlt : b.val < p.length := by omega
        have := (p.adj_getVert_succ hlt).symm
        rwa [h] at this
    · intro hadj
      have h1 : G.dist (p.getVert a.val) (p.getVert b.val) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have hdd := dist_getVert_of_shortest' G p hp ha hb
      rw [h1] at hdd
      rcases le_total a.val b.val with h | h
      · rw [max_eq_right h, min_eq_left h] at hdd; omega
      · rw [max_eq_left h, min_eq_right h] at hdd; omega

end Exhaustion


/-- AUDIT-NOTES A6, exhaustion. A connected pair graph that is not a double star contains an
induced cycle (a shortest cycle) or an induced `P₅` (five consecutive vertices of a geodesic
in a tree of diameter at least four). -/
theorem exhaustion (Γ : PairGraph) (hconn : Γ.G.Connected) (hnot : ¬ IsDoubleStarForest Γ.G) :
    (∃ (m : ℕ) (_ : 3 ≤ m) (φ : Fin m → Γ.V), Function.Injective φ ∧
        ∀ u v : Fin m, (cycleAdj m).Adj u v ↔ Γ.G.Adj (φ u) (φ v)) ∨
      (∃ φ : Fin 5 → Γ.V, Function.Injective φ ∧
        ∀ u v : Fin 5, (pathAdj 5).Adj u v ↔ Γ.G.Adj (φ u) (φ v)) := by
  -- Connectivity is not needed: both branches are produced from `hnot` alone.
  let _ := hconn
  by_cases hac : Γ.G.IsAcyclic
  · -- A forest that is not a double-star forest has two vertices at distance at least four,
    -- and five consecutive vertices of a geodesic between them induce a `P₅`.
    refine Or.inr ?_
    have hb : ¬ ∀ u v : Γ.V, Γ.G.Reachable u v → Γ.G.dist u v ≤ 3 := fun h => hnot ⟨hac, h⟩
    push Not at hb
    obtain ⟨u, v, -, hdist⟩ := hb
    exact Exhaustion.induced_path5_of_dist Γ.G u v (by omega)
  · -- Otherwise a shortest cycle is induced.
    exact Or.inl (Exhaustion.induced_cycle_of_not_acyclic Γ.G hac)


end TriangleInflation.Graph
