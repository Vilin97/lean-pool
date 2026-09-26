/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module
public import Mathlib.Data.Fintype.Order

public import LeanPool.OrderClosures.Solovay
public import LeanPool.OrderClosures.GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm


/-!
# The Gao--Leung problem and counterexamples

Formalization of the paper's counterexamples concerning order and unbounded-order
adherences of sublattices and solid sets.
-/

@[expose] public section

namespace OrderClosures

open Set

universe u v

section GaoLeungTheorem

/-- The Gao--Leung question, as a predicate on an ambient vector lattice. -/
def GaoLeungProperty (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop :=
  ∀ Y : VectorSublattice X, IsOrderClosed (uoAdherence (Y : Set X))

end GaoLeungTheorem

section Counterexample

/-- Paper Theorem 2.1: an order-complete `C(K)` of arbitrarily large density,
with a closed separable sublattice whose order closure is all of `C(K)`. -/
theorem gao_counterexample (κ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K),
      IsOrderComplete C(K, ℝ) ∧ κ ≤ densityCharacter C(K, ℝ) ∧
      ∃ Y : VectorSublattice C(K, ℝ),
        IsClosed (Y : Set C(K, ℝ)) ∧
          TopologicalSpace.IsSeparable (Y : Set C(K, ℝ)) ∧
          ∀ Z : VectorSublattice C(K, ℝ),
            Y ≤ Z → IsOrderClosed (Z : Set C(K, ℝ)) → Z = ⊤ := by
  induction κ using Cardinal.inductionOn with
  | _ Gamma =>
    classical
    obtain ⟨lin, wf⟩ := exists_wellFoundedLT Gamma
    let : LinearOrder Gamma := lin
    let : WellFoundedLT Gamma := wf
    let : TopologicalSpace Gamma := ⊥
    let : DiscreteTopology Gamma := ⟨rfl⟩
    let B := RegularOpen (SolovayProduct Gamma)
    let K := BooleanStone B
    refine ⟨K, inferInstance, inferInstance, inferInstance,
      isOrderComplete_continuousMap K, ?_,
      solovayVectorSublattice Gamma,
      isClosed_solovayVectorSublattice Gamma,
      isSeparable_solovayVectorSublattice Gamma, ?_⟩
    · calc
        Cardinal.mk Gamma ≤ Cardinal.mk B :=
          Cardinal.mk_le_of_injective (solovayA_injective Gamma 0)
        _ ≤ densityCharacter C(K, ℝ) :=
          cardinalMk_le_densityCharacter_booleanStoneContinuousMap B
    · intro Z hYZ hZorder
      exact solovayVectorSublattice_maximalOrderClosed Gamma Z hYZ hZorder

/-- Paper Remark `rem:gao-cardinality`: cardinality of an arbitrary order adherence. -/
theorem orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     (D : Set X) :
    Cardinal.mk (orderAdherence D) ≤
      (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
  let Φ : orderAdherence D → Set (Set D) := fun x ↦
    {A | x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A)}
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    rcases x.2 with ⟨ι, hpre, hdir, hnon, f, hfD, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hnon
    rcases hfx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnonneg, hrglb, hbound⟩
    let : Preorder κ := hκpre
    let : IsDirected κ (· ≤ ·) := hκdir
    let : Nonempty κ := hκnon
    have hk : ∃ k, ¬ |x.1 - y.1| ≤ r k := by
      by_contra hk
      push Not at hk
      have hlower : |x.1 - y.1| ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        exact hk k
      have habs : |x.1 - y.1| = 0 :=
        le_antisymm (hrglb.2 hlower) (abs_nonneg _)
      exact hne (sub_eq_zero.mp ((abs_eq_zero_iff_zero _).mp habs))
    obtain ⟨k, hk⟩ := hk
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (hbound k)
    let fD : ι → D := fun i ↦ ⟨f i, hfD i⟩
    let A : Set D := Set.range (fun i : Set.Ici i₀ ↦ fD i.1)
    have hIci : DirectedOn (· ≤ ·) (Set.Ici i₀) := by
      intro a ha b hb
      obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
      exact ⟨c, ha.trans hac, hac, hbc⟩
    let : IsDirectedOrder (Set.Ici i₀) := hIci.isDirectedOrder
    let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
    have hrestrict : OrderConvergesTo (fun i : Set.Ici i₀ ↦ f i.1) x.1 := by
      refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnonneg,
        hrglb, ?_⟩
      intro l
      obtain ⟨i₁, hi₁⟩ := Filter.eventually_atTop.mp (hbound l)
      obtain ⟨m, hi₀m, hi₁m⟩ := directed_of (· ≤ ·) i₀ i₁
      apply Filter.eventually_atTop.mpr
      refine ⟨⟨m, hi₀m⟩, ?_⟩
      intro j hj
      exact hi₁ j.1 (hi₁m.trans hj)
    have hxA : x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) := by
      refine ⟨Set.Ici i₀, inferInstance, inferInstance, inferInstance,
        fun i ↦ f i.1, ?_, hrestrict⟩
      intro i
      exact ⟨fD i.1, ⟨i, rfl⟩, rfl⟩
    have hxA' : A ∈ Φ x := hxA
    have hyA' : A ∈ Φ y := by
      rw [← hxy]
      exact hxA'
    change y.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) at hyA'
    rcases hyA' with ⟨τ, hτpre, hτdir, hτnon, a, haA, hay⟩
    let : Preorder τ := hτpre
    let : IsDirected τ (· ≤ ·) := hτdir
    let : Nonempty τ := hτnon
    have habound : ∀ j, |a j - x.1| ≤ r k := by
      intro j
      rcases haA j with ⟨z, ⟨i, rfl⟩, hza⟩
      rw [← hza]
      exact hi₀ i.1 i.2
    have hybound : |y.1 - x.1| ≤ r k :=
      (hay.sub (orderConvergesTo_const x.1)).abs.le_of_forall_le habound
    exact hk (by simpa [abs_sub_comm] using hybound)
  calc
    Cardinal.mk (orderAdherence D) ≤ Cardinal.mk (Set (Set D)) :=
      Cardinal.mk_le_of_injective hΦ
    _ = (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
      rw [Cardinal.mk_set, Cardinal.mk_set]

/-- Paper Proposition `prop:solid-large-order-closure`. -/
theorem exists_solid_large_orderAdherence (κ : Cardinal.{u}) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.aleph0 ∧
        κ ≤ solidGeneratorNumber (orderAdherence S) := by
  induction κ using Cardinal.inductionOn with
  | _ Γ =>
    let X := Option Γ → ℕ → ℝ
    let g : ℕ → X := fun n _ m ↦ if m ≤ n then (n + 1 : ℕ) else 0
    let S : Set X := solidHull (Set.range g)
    refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, S,
      LatticeOrderedAddCommGroup.isSolid_solidClosure _, ?_, ?_⟩
    · apply le_antisymm
      · calc
          solidGeneratorNumber S ≤ Cardinal.mk (Set.range g) := by
            apply csInf_le'
            exact ⟨Set.range g, rfl, rfl⟩
          _ ≤ Cardinal.aleph0 := by
            simpa [Cardinal.mk_nat] using Cardinal.mk_range_le_lift (f := g)
      · apply le_csInf
        · exact ⟨Cardinal.mk (Set.range g), Set.range g, rfl, rfl⟩
        · intro c hc
          rcases hc with ⟨A, hAc, hAS⟩
          rw [← hAc]
          by_contra hAfin
          have hAlt : Cardinal.mk A < Cardinal.aleph0 := lt_of_not_ge hAfin
          let : Finite A := Cardinal.mk_lt_aleph0_iff.mp hAlt
          have hchoice : ∀ a : A, ∃ n, |a.1| ≤ |g n| := by
            intro a
            have haS : a.1 ∈ S := by
              rw [← hAS]
              exact ⟨a.1, a.2, le_rfl⟩
            rcases haS with ⟨b, ⟨n, rfl⟩, hab⟩
            exact ⟨n, hab⟩
          choose N hN using hchoice
          obtain ⟨M, hM⟩ := Finite.exists_le N
          have hgS : g (M + 1) ∈ S := ⟨g (M + 1), ⟨M + 1, rfl⟩, le_rfl⟩
          rw [← hAS] at hgS
          rcases hgS with ⟨a, haA, hga⟩
          let aa : A := ⟨a, haA⟩
          have ha0 := hN aa (none : Option Γ) (M + 1)
          have hga0 := hga (none : Option Γ) (M + 1)
          have hNM := hM aa
          dsimp [g, X] at ha0 hga0
          rw [ite_eq_right (by omega)] at ha0
          simp only [abs_zero] at ha0
          rw [ite_eq_left (by omega)] at hga0
          norm_num at hga0
          change |a none (M + 1)| ≤ 0 at ha0
          have hpos : (0 : ℝ) < |(M : ℝ) + 1 + 1| := by positivity
          linarith
    · have hadh : orderAdherence S = Set.univ := by
        ext f
        simp only [Set.mem_univ, iff_true]
        have hsolid : LatticeOrderedAddCommGroup.IsSolid (orderAdherence S) := by
          rw [orderAdherence_eq_solidOrderAdherence
            (LatticeOrderedAddCommGroup.isSolid_solidClosure (Set.range g))]
          exact LatticeOrderedAddCommGroup.isSolid_solidClosure _
        apply hsolid (x := |f|) (y := f)
        · let I := ULift.{u} ℕ
          let p : I → X := fun n ↦ |f| ⊓ g n.down
          have hg_nonneg : ∀ n, 0 ≤ g n := by
            intro n γ m
            simp only [g, X]
            split_ifs <;> positivity
          have hg_mono : Monotone g := by
            intro n k hnk γ m
            simp only [g, X]
            by_cases hmn : m ≤ n
            · rw [ite_eq_left hmn, ite_eq_left (hmn.trans hnk)]
              exact_mod_cast Nat.succ_le_succ hnk
            · rw [ite_eq_right hmn]
              split_ifs <;> positivity
          have hp_mono : Monotone p := fun _ _ hnk ↦
            inf_le_inf_left _ (hg_mono hnk)
          have hp_lub : IsLUB (Set.range p) |f| := by
            constructor
            · rintro _ ⟨n, rfl⟩
              exact inf_le_left
            · intro c hc γ m
              obtain ⟨k, hk⟩ := exists_nat_ge |f γ m|
              let n := max m k
              have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_max_right m k
              have hfn : |f γ m| ≤ (n + 1 : ℕ) := by
                norm_num
                linarith
              have hcn := hc ⟨ULift.up n, rfl⟩ γ m
              dsimp [p, g, X, n] at hcn
              rw [ite_eq_left (Nat.le_max_left m k)] at hcn
              rw [inf_eq_left.mpr (by simpa [n] using hfn)] at hcn
              exact hcn
          refine ⟨I, inferInstance, inferInstance, inferInstance, p, ?_,
            orderConvergesTo_of_monotone_isLUB hp_mono hp_lub⟩
          intro n
          refine ⟨g n.down, ⟨n.down, rfl⟩, ?_⟩
          have hp_nonneg : 0 ≤ p n := le_inf (abs_nonneg f) (hg_nonneg n.down)
          rw [abs_of_nonneg hp_nonneg, abs_of_nonneg (hg_nonneg n.down)]
          exact (inf_le_right : |f| ⊓ g n.down ≤ g n.down)
        · simp
      rw [hadh]
      apply le_csInf
      · refine ⟨Cardinal.mk (Set.univ : Set X), Set.univ, rfl, ?_⟩
        ext x
        constructor
        · exact fun _ ↦ Set.mem_univ x
        · intro _
          exact ⟨x, Set.mem_univ x, le_rfl⟩
      · intro c hc
        rcases hc with ⟨A, hAc, hAuniv⟩
        rw [← hAc]
        by_contra hsmall
        have hlt : Cardinal.mk A < Cardinal.mk Γ := lt_of_not_ge hsmall
        obtain ⟨e⟩ := (Cardinal.le_def A Γ).mp hlt.le
        let d : Γ → ℝ := Function.extend e
          (fun a : A ↦ |a.1 (some (e a)) 0| + 1) (fun _ ↦ 0)
        let f : X := fun γ m ↦ match γ, m with
          | some δ, 0 => d δ
          | _, _ => 0
        have hfA : f ∈ solidHull A := by
          rw [hAuniv]
          exact Set.mem_univ f
        rcases hfA with ⟨a, haA, hfa⟩
        let aa : A := ⟨a, haA⟩
        have hcoord := hfa (some (e aa)) 0
        change |f (some (e aa)) 0| ≤ |a (some (e aa)) 0| at hcoord
        change |Function.extend (⇑e) (fun a : A => |a.1 (some (e a)) 0| + 1)
          (fun _ => 0) (e aa)| ≤ |a (some (e aa)) 0| at hcoord
        rw [Function.Injective.extend_apply e.injective] at hcoord
        rw [abs_of_nonneg (by positivity)] at hcoord
        linarith [abs_nonneg (a (some (e aa)) 0)]

/-- The class of all suprema of subsets of the positive part of `S`, used in
the proof of Proposition `prop:cardinalitybound`. -/
def positiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X]
    (S : Set X) : Set X :=
  {x | ∃ A : Set X, A ⊆ S ∩ Ici 0 ∧ IsLUB A x}

/-- The order-closed envelope used for the cardinality estimate. -/
def signedPositiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X]
    (S : Set X) : Set X :=
  {x | x⁺ ∈ positiveSubsetSuprema S ∧ x⁻ ∈ positiveSubsetSuprema S}

/-- Isolates the order-closedness of positive subset suprema so it can be
reused for the signed envelope in `signedPositiveSubsetSuprema_isOrderClosed`. -/
theorem positiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (positiveSubsetSuprema S) := by
  have hnonneg : ∀ {z : X}, z ∈ positiveSubsetSuprema S → 0 ≤ z := by
    intro z hz
    rcases hz with ⟨A, hAS, hAlub⟩
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      exact (hAS ha).2.trans (hAlub.1 ha)
    · have hupper : z ≤ z + z := hAlub.2 fun a ha ↦ (hA ⟨a, ha⟩).elim
      exact nonneg_of_le_add_right hupper
  have hdown : ∀ {y z : X}, 0 ≤ y → y ≤ z →
      z ∈ positiveSubsetSuprema S → y ∈ positiveSubsetSuprema S := by
    intro y z hy0 hyz hz
    rcases hz with ⟨A, hAS, hAlub⟩
    let B : Set X := (fun a ↦ a ⊓ y) '' A
    refine ⟨B, ?_, ?_⟩
    · rintro b ⟨a, ha, rfl⟩
      have ha0 : 0 ≤ a := (hAS ha).2
      have hab0 : 0 ≤ a ⊓ y := le_inf ha0 hy0
      have habs : |a ⊓ y| ≤ |a| := by
        simp [abs_of_nonneg hab0, abs_of_nonneg ha0]
      exact ⟨hS (hAS ha).1 habs, hab0⟩
    · constructor
      · rintro b ⟨a, ha, rfl⟩
        exact inf_le_right
      · intro w hw
        have hupperA : z + w - y ∈ upperBounds A := by
          intro a ha
          have haz : a ≤ z := hAlub.1 ha
          have haw : a ⊓ y ≤ w := hw ⟨a, ha, rfl⟩
          change a ≤ z + w - y
          calc
            a = (a - a ⊓ y) + (a ⊓ y) := by abel
            _ ≤ (z - y) + w := add_le_add (by
              rw [sub_inf_eq_posPart]
              exact (posPart_mono (sub_le_sub_right haz y)).trans_eq
                (posPart_of_nonneg (sub_nonneg.mpr hyz))) haw
            _ = z + w - y := by abel
        have hzw := hAlub.2 hupperA
        change y ≤ w
        apply sub_nonpos.mp
        have hcancel := sub_le_sub_left hzw z
        convert hcancel using 1 <;> abel
  intro x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  let : Preorder ι := hpre
  let : IsDirected ι (· ≤ ·) := hdir
  let : Nonempty ι := hne
  have hf0 : ∀ i, 0 ≤ f i := fun i ↦ hnonneg (hf i)
  have hx0 : 0 ≤ x := hfx.nonneg hf0
  rcases hfx with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκne
  let y : κ → X := fun k ↦ (x - r k)⁺
  have hy_lub : IsLUB (Set.range y) x := by
    constructor
    · rintro _ ⟨k, rfl⟩
      exact show (x - r k) ⊔ 0 ≤ x from
        sup_le (sub_le_self _ (hrnonneg k)) hx0
    · intro c hc
      have hlow : x - c ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        have hraw : x - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
        exact sub_le_iff_le_add.mpr (by
          simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
      exact sub_nonpos.mp (hrglb.2 hlow)
  have hy : ∀ k, y k ∈ positiveSubsetSuprema S := by
    intro k
    obtain ⟨i, hi⟩ := (hbound k).exists
    have hyfi : y k ≤ f i := by
      dsimp [y]
      have hi' : |x - f i| ≤ r k := by simpa [abs_sub_comm] using hi
      have hsub : x - f i ≤ r k := (le_abs_self _).trans hi'
      have hraw : x - r k ≤ f i := sub_le_iff_le_add.mpr (by
        simpa [add_comm] using (sub_le_iff_le_add.mp hsub))
      exact sup_le hraw (hf0 i)
    exact hdown (posPart_nonneg _) hyfi (hf i)
  choose A hAS hAlub using hy
  let B : Set X := {a | ∃ k, a ∈ A k}
  refine ⟨B, ?_, ?_⟩
  · rintro a ⟨k, ha⟩
    exact hAS k ha
  · constructor
    · rintro a ⟨k, ha⟩
      exact (hAlub k).1 ha |>.trans (hy_lub.1 ⟨k, rfl⟩)
    · intro c hc
      apply hy_lub.2
      rintro _ ⟨k, rfl⟩
      exact (hAlub k).2 fun a ha ↦ hc ⟨k, ha⟩

/-- Unnumbered assertion in the proof of `prop:cardinalitybound`. -/
theorem signedPositiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (signedPositiveSubsetSuprema S) := by
  intro x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  let : Preorder ι := hpre
  let : IsDirected ι (· ≤ ·) := hdir
  let : Nonempty ι := hne
  have hpos : OrderConvergesTo (fun i ↦ (f i)⁺) x⁺ := by
    simpa [posPart] using hfx.sup (orderConvergesTo_const (0 : X))
  have hneg : OrderConvergesTo (fun i ↦ (f i)⁻) x⁻ := by
    simpa [negPart, posPart] using hfx.neg.sup (orderConvergesTo_const (0 : X))
  constructor
  · exact positiveSubsetSuprema_isOrderClosed hS
      ⟨ι, inferInstance, inferInstance, inferInstance, fun i ↦ (f i)⁺,
        fun i ↦ (hf i).1, hpos⟩
  · exact positiveSubsetSuprema_isOrderClosed hS
      ⟨ι, inferInstance, inferInstance, inferInstance, fun i ↦ (f i)⁻,
        fun i ↦ (hf i).2, hneg⟩

/-- Paper Proposition `prop:cardinalitybound`. -/
theorem solid_orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
     {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    Cardinal.mk (orderAdherence S) ≤ (2 : Cardinal) ^ Cardinal.mk S := by
  let E := signedPositiveSubsetSuprema S
  have hSE : S ⊆ E := by
    intro s hs
    constructor
    · refine ⟨{s⁺}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hspos : |s⁺| ≤ |s| := by
        rw [abs_of_nonneg (posPart_nonneg s)]
        exact posPart_le_abs s
      exact ⟨hS hs hspos, posPart_nonneg s⟩
    · refine ⟨{s⁻}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hsneg : |s⁻| ≤ |s| := by
        rw [abs_of_nonneg (negPart_nonneg s)]
        exact negPart_le_abs s
      exact ⟨hS hs hsneg, negPart_nonneg s⟩
  have hadhE : orderAdherence S ⊆ E := fun _ hx ↦
    signedPositiveSubsetSuprema_isOrderClosed hS (orderAdherence_mono hSE hx)
  let Aplus : E → Set X := fun x ↦ Classical.choose x.2.1
  let Aminus : E → Set X := fun x ↦ Classical.choose x.2.2
  have hAplus : ∀ x : E,
      Aplus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aplus x) x.1⁺ := fun x ↦
    Classical.choose_spec x.2.1
  have hAminus : ∀ x : E,
      Aminus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aminus x) x.1⁻ := fun x ↦
    Classical.choose_spec x.2.2
  let Ψ : E → Set S := fun x ↦
    {s | s.1 ∈ Aplus x ∨ -s.1 ∈ Aminus x}
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have hplus_le : x.1⁺ ≤ y.1⁺ := (hAplus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAplus x).1 ha).1
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := Or.inl ha
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hay | hnega
        · exact (hAplus y).2.1 hay
        · have hnega0 : 0 ≤ -a := ((hAminus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus x).1 ha).2
          exact (ha0 this).elim
    have hplus_ge : y.1⁺ ≤ x.1⁺ := (hAplus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAplus y).1 ha).1
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := Or.inl ha
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hax | hnega
        · exact (hAplus x).2.1 hax
        · have hnega0 : 0 ≤ -a := ((hAminus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus y).1 ha).2
          exact (ha0 this).elim
    have hminus_le : x.1⁻ ≤ y.1⁻ := (hAminus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAminus x).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          right
          simpa using ha
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hnega | hay
        · have hnega0 : 0 ≤ -a := ((hAplus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus x).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus y).2.1 (by simpa using hay)
    have hminus_ge : y.1⁻ ≤ x.1⁻ := (hAminus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have haS : a ∈ S := ((hAminus y).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          right
          simpa using ha
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hnega | hax
        · have hnega0 : 0 ≤ -a := ((hAplus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus y).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus x).2.1 (by simpa using hax)
    apply Subtype.ext
    calc
      x.1 = x.1⁺ - x.1⁻ := (posPart_sub_negPart x.1).symm
      _ = y.1⁺ - y.1⁻ := by
        rw [le_antisymm hplus_le hplus_ge, le_antisymm hminus_le hminus_ge]
      _ = y.1 := posPart_sub_negPart y.1
  let θ : orderAdherence S → E := fun x ↦ ⟨x.1, hadhE x.2⟩
  have hθ : Function.Injective θ := fun x y hxy ↦ by
    apply Subtype.ext
    dsimp [θ] at hxy
    exact congrArg (fun z : E ↦ z.1) hxy
  calc
    Cardinal.mk (orderAdherence S) ≤ Cardinal.mk E := Cardinal.mk_le_of_injective hθ
    _ ≤ Cardinal.mk (Set S) := Cardinal.mk_le_of_injective hΨ
    _ = (2 : Cardinal) ^ Cardinal.mk S := Cardinal.mk_set

end Counterexample

end OrderClosures
