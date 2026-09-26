/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Convergences.Order
public import LeanPool.OrderClosures.BanLat.Normed
public import LeanPool.OrderClosures.BanLat.OrderComplete


/-!
# Order continuous norms — basic theory

A normed vector lattice has an **order continuous norm** when every decreasing
net of non-negative elements with infimum zero converges to zero in norm. The
sequential version is **σ-order continuity**; equivalently, every increasing
positive sequence whose supremum exists converges in norm to that supremum.

This file introduces the σ- and full classes `IsSigmaOrderContinuousNorm` and
`IsOrderContinuousNorm`, records that the latter is stronger, proves the
equivalent sequential characterisations of σ-order continuity, and shows that
an order continuous Banach lattice is order complete.
-/

@[expose] public section

universe u

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-! ### Definitions -/

/-- A normed vector lattice has a **σ-order continuous norm** if every antitone
sequence of non-negative elements with greatest lower bound zero converges to
zero in norm. -/
class IsSigmaOrderContinuousNorm (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {u : ℕ → X}, Antitone u → (∀ n, 0 ≤ u n) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- A normed vector lattice has an **order continuous norm** if every antitone
net of non-negative elements (over a non-empty directed index set) with
greatest lower bound zero converges to zero in norm.

The index set `ι` is constrained to live in the same universe as `X`; in
applications (e.g. indexing by a subset of `X`) this is the case. -/
class IsOrderContinuousNorm (X : Type u) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → X}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- In a normed vector lattice with order-continuous norm, order convergence of a net implies
norm convergence. -/
theorem tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [IsOrderContinuousNorm X]
    {ι : Type u} [Preorder ι]
    {x : ι → X} {a : X} (hx : OrderConvergesTo x a) :
    Filter.Tendsto x Filter.atTop (nhds a) := by
  rcases hx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  have hr_tend : Filter.Tendsto r Filter.atTop (nhds 0) :=
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hranti hrnn hrglb
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr_event := Metric.tendsto_nhds.mp hr_tend ε hε
  rcases hr_event.exists with ⟨k, hk⟩
  refine (hrevent k).mono fun i hi => ?_
  have hnorm_le : ‖x i - a‖ ≤ ‖r k‖ := by
    rw [← norm_abs_eq_norm (x i - a)]
    exact norm_le_norm_of_abs_le_abs (by
      rw [abs_abs, abs_of_nonneg (hrnn k)]
      exact hi)
  calc
    dist (x i) a = ‖x i - a‖ := dist_eq_norm _ _
    _ ≤ ‖r k‖ := hnorm_le
    _ = dist (r k) 0 := by rw [dist_eq_norm, sub_zero]
    _ < ε := hk

/-- An order continuous norm is in particular σ-order continuous. -/
instance (priority := 100)
    IsOrderContinuousNorm.toIsSigmaOrderContinuousNorm {X : Type u}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [h : IsOrderContinuousNorm X] :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Transfer the ℕ-indexed sequence to the universe of `X` via `ULift`.
  let u' : ULift.{u, 0} ℕ → X := fun n => u n.down
  have hu'_anti : Antitone u' := fun a b h => hanti (by exact h)
  have hu'_nn : ∀ i, 0 ≤ u' i := fun i => hnn i.down
  have hu'_glb : IsGLB (Set.range u') 0 := by
    have hrange : Set.range u' = Set.range u := by
      ext z; constructor
      · rintro ⟨⟨n⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨⟨n⟩, rfl⟩
    rw [hrange]; exact hglb
  have htend := h.tendsto_of_antitone_isGLB_zero hu'_anti hu'_nn hu'_glb
  -- Pull back to ℕ: the map `n ↦ ⟨n⟩ : ℕ → ULift ℕ` is order isomorphic.
  have : Filter.Tendsto (fun n : ℕ => u' ⟨n⟩) Filter.atTop (nhds 0) := by
    refine htend.comp ?_
    refine Filter.tendsto_atTop.mpr fun ⟨b⟩ => ?_
    exact Filter.eventually_atTop.mpr ⟨b, fun n hn => hn⟩
  exact this

namespace IsSigmaOrderContinuousNorm

variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]

/-! ### Equivalent sequential characterisations -/

/-- An increasing sequence with a least upper bound converges in norm to
that bound. -/
theorem tendsto_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Define v n = x - u n, which is antitone, nonneg, with GLB 0
  have hv_anti : Antitone (fun n => x - u n) :=
    fun _ _ h => sub_le_sub_left (hmono h) x
  have hv_nn : ∀ n, 0 ≤ x - u n :=
    fun n => sub_nonneg.mpr (hlub.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => x - u n)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, y ≤ x - w := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_comm.mp (hw ⟨n, rfl⟩)
      have h := hlub.2 hlb
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.const_sub x using 1
  · ext n; abel
  · abel_nf

/-- An antitone sequence with a greatest lower bound converges in norm to
that bound. -/
theorem tendsto_of_antitone_isGLB {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_anti : Antitone (fun n => u n - x) :=
    fun _ _ h => sub_le_sub_right (hanti h) x
  have hv_nn : ∀ n, 0 ≤ u n - x :=
    fun n => sub_nonneg.mpr (hglb.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => u n - x)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, w + x ≤ y := by
        rintro _ ⟨n, rfl⟩
        exact add_le_of_le_sub_right (hw ⟨n, rfl⟩)
      have h := hglb.2 hlb
      rwa [add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.add tendsto_const_nhds using 1
  · ext n; abel
  · abel_nf

/-- The norm is σ-order continuous: if `|u n - x| ≤ v n` for an antitone
sequence `v` with `inf v = 0`, then `u n → x` in norm. -/
theorem tendsto_of_abs_sub_le_antitone {u : ℕ → X} {v : ℕ → X} {x : X}
    (hv_anti : Antitone v) (hv_nn : ∀ n, 0 ≤ v n)
    (hv_glb : IsGLB (Set.range v) 0)
    (hle : ∀ n, |u n - x| ≤ v n) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_tend := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  have hnorm_le : ∀ n, ‖u n - x‖ ≤ ‖v n‖ := fun n =>
    norm_le_norm_of_abs_le_abs ((hle n).trans (le_abs_self _))
  have hv_norm := hv_tend.norm
  rw [norm_zero] at hv_norm
  have h0 := squeeze_zero_norm hnorm_le hv_norm
  exact tendsto_sub_nhds_zero_iff.mp h0

/-- The norm itself is an order continuous function on positive elements:
if `u n` converges in order to `x`, then `‖u n‖ → ‖x‖`. -/
theorem tendsto_norm_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u)
    (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖x‖) :=
  (tendsto_of_monotone_isLUB hmono hlub).norm

end IsSigmaOrderContinuousNorm

/-! ### Order continuity implies order completeness -/

namespace BanachLattice

variable [BanachLattice X]

omit [BanachLattice X] in
/-- Archimedean "gap" lemma. In an Archimedean
vector lattice, any common lower bound of all differences `w - a` with `w` an
upper bound of a nonempty bounded-above set `A` and `a ∈ A` must be `≤ 0`. -/
lemma le_zero_of_lb_upperBounds_sub [IsVLArchimedean X]
    {A : Set X} (hne : A.Nonempty) (hbd : BddAbove A) {ε : X}
    (hε : ∀ w ∈ upperBounds A, ∀ a ∈ A, ε ≤ w - a) : ε ≤ 0 := by
  have key : ∀ n : ℕ, ∀ w ∈ upperBounds A, ∀ a ∈ A, n • ε ≤ w - a := by
    intro n
    induction n with
    | zero =>
        intro w hw a ha
        simpa using sub_nonneg.mpr (hw ha)
    | succ k ih =>
        intro w hw a ha
        have hub : w - k • ε ∈ upperBounds A := fun s hs =>
          le_sub_comm.mp (ih w hw s hs)
        have hstep : ε ≤ (w - k • ε) - a := hε _ hub a ha
        have h : k • ε + ε ≤ k • ε + ((w - k • ε) - a) :=
          add_le_add (le_refl (k • ε)) hstep
        have h3 : k • ε + ((w - k • ε) - a) = w - a := by abel
        rw [h3] at h
        simpa [succ_nsmul] using h
  obtain ⟨w₀, hw₀⟩ := hbd
  obtain ⟨a₀, ha₀⟩ := hne
  exact isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp inferInstance
    (fun n => key n w₀ hw₀ a₀ ha₀)

/-- An order continuous Banach lattice is order complete. -/
@[reducible]
noncomputable def conditionallyCompleteLatticeOfIsOrderContinuousNorm
    [IsOrderContinuousNorm X] :
    ConditionallyCompleteLattice X := by
  haveI : Nonempty X := ⟨0⟩
  refine conditionallyCompleteLatticeOfPosSet X
    (fun {S} _ hSne hSbdd => ?_)
  obtain ⟨w₀, hw₀⟩ := hSbdd
  obtain ⟨s₀, hs₀⟩ := hSne
  classical
  -- Index: (upper bound of S) ×ᵒᵈ (nonempty finite subset of S), ordered so
  -- that upper bounds decrease and finite subsets increase.
  let Ub : Type _ := {w : X // w ∈ upperBounds S}
  let Fn : Type _ := {F : Finset X // (↑F : Set X) ⊆ S ∧ F.Nonempty}
  let I : Type _ := Ubᵒᵈ × Fn
  have : Nonempty Ub := ⟨⟨w₀, hw₀⟩⟩
  have : Nonempty Fn := ⟨⟨{s₀}, by
    refine ⟨?_, Finset.singleton_nonempty s₀⟩
    intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact hs₀⟩⟩
  have : Nonempty I := instNonemptyProd
  have : IsDirected Fn (· ≤ ·) := by
    refine ⟨fun F G => ?_⟩
    refine ⟨⟨F.val ∪ G.val, ?_, F.prop.2.mono Finset.subset_union_left⟩,
            Finset.subset_union_left, Finset.subset_union_right⟩
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact F.prop.1 h
    · exact G.prop.1 h
  have : IsDirected Ubᵒᵈ (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    refine ⟨OrderDual.toDual ⟨(OrderDual.ofDual a).val ⊓ (OrderDual.ofDual b).val,
      fun s hs => le_inf ((OrderDual.ofDual a).prop hs) ((OrderDual.ofDual b).prop hs)⟩,
      ?_, ?_⟩
    · change (_ : Ub) ≤ OrderDual.ofDual a
      exact inf_le_left
    · change (_ : Ub) ≤ OrderDual.ofDual b
      exact inf_le_right
  have : IsDirected I (· ≤ ·) := by
    refine ⟨fun p q => ?_⟩
    obtain ⟨c, hac, hbc⟩ := (‹IsDirected Ubᵒᵈ (· ≤ ·)›).directed p.1 q.1
    obtain ⟨d, had, hbd⟩ := (‹IsDirected Fn (· ≤ ·)›).directed p.2 q.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩
  -- The antitone net `z` on `I`: `z (w, F) = w - sup' F`.
  let z : I → X := fun p =>
    (OrderDual.ofDual p.1).val - p.2.val.sup' p.2.prop.2 id
  have hFle : ∀ p : I, p.2.val.sup' p.2.prop.2 id ≤ (OrderDual.ofDual p.1).val :=
    fun p => Finset.sup'_le _ _ fun x hx =>
      (OrderDual.ofDual p.1).prop (p.2.prop.1 hx)
  have hz_nn : ∀ p : I, 0 ≤ z p := fun p => sub_nonneg.mpr (hFle p)
  have hz_anti : Antitone z := by
    intro p q hpq
    have h1 : (OrderDual.ofDual q.1).val ≤ (OrderDual.ofDual p.1).val := hpq.1
    have h2 : p.2.val ⊆ q.2.val := hpq.2
    have hsup : p.2.val.sup' p.2.prop.2 id ≤ q.2.val.sup' q.2.prop.2 id :=
      Finset.sup'_mono _ h2 p.2.prop.2
    exact sub_le_sub h1 hsup
  have hz_glb : IsGLB (Set.range z) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, rfl⟩; exact hz_nn p
    · intro ε hε
      -- `ε` is a lower bound of range `z`; apply the Archimedean gap lemma.
      refine le_zero_of_lb_upperBounds_sub ⟨s₀, hs₀⟩ ⟨w₀, hw₀⟩ ?_
      intro w hw a ha
      -- Form the element `(w, {a})` of `I` and evaluate `z`.
      let p : I := (OrderDual.toDual ⟨w, hw⟩,
        ⟨{a}, by
          refine ⟨?_, Finset.singleton_nonempty a⟩
          intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact ha⟩)
      have hzp : z p = w - a := by
        simp [z, p, Finset.sup'_singleton]
      have := hε ⟨p, rfl⟩
      rw [hzp] at this
      exact this
  -- Apply OCN to get `z → 0` in norm.
  have htend : Filter.Tendsto z Filter.atTop (nhds 0) :=
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hz_anti hz_nn hz_glb
  -- Extract from `htend` that the monotone net `u_F = sup' F` is norm-Cauchy.
  let u : Fn → X := fun F => F.val.sup' F.prop.2 id
  have hu_mono : Monotone u := fun F G h => Finset.sup'_mono _ h F.prop.2
  have hu_cauchy : Cauchy (Filter.map u Filter.atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    rw [Metric.tendsto_nhds] at htend
    have hev := htend (ε/2) (by linarith)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨p₀, hp₀⟩ := hev
    refine ⟨u '' {F | p₀.2 ≤ F}, ?_, ?_⟩
    · exact Filter.image_mem_map (Filter.mem_atTop p₀.2)
    · rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
      have hpF : p₀ ≤ (p₀.1, F) := ⟨le_refl _, hF⟩
      have hpG : p₀ ≤ (p₀.1, G) := ⟨le_refl _, hG⟩
      have h1 : dist (z (p₀.1, F)) 0 < ε/2 := hp₀ _ hpF
      have h2 : dist (z (p₀.1, G)) 0 < ε/2 := hp₀ _ hpG
      rw [dist_zero_right] at h1 h2
      have hzF : z (p₀.1, F) = (OrderDual.ofDual p₀.1).val - u F := rfl
      have hzG : z (p₀.1, G) = (OrderDual.ofDual p₀.1).val - u G := rfl
      rw [dist_eq_norm]
      have heq : u F - u G = z (p₀.1, G) - z (p₀.1, F) := by
        rw [hzF, hzG]; abel
      rw [heq]
      have : ‖z (p₀.1, G) - z (p₀.1, F)‖ ≤ ‖z (p₀.1, G)‖ + ‖z (p₀.1, F)‖ := by
        rw [sub_eq_add_neg]
        exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
      linarith
  -- By Banach completeness, `u` has a limit `x`.
  obtain ⟨x, hx_tend⟩ := CompleteSpace.complete hu_cauchy
  -- `x` is the LUB of range of `u`, which equals LUB of `S`.
  have hx_lub : IsLUB (Set.range u) x :=
    isLUB_of_tendsto_atTop hu_mono hx_tend
  refine ⟨x, ?_, ?_⟩
  · -- `x` is an upper bound of `S`
    intro s hs
    have hprop : (↑({s} : Finset X) : Set X) ⊆ S ∧ ({s} : Finset X).Nonempty := by
      refine ⟨?_, Finset.singleton_nonempty s⟩
      intro y hy; rcases Finset.mem_singleton.mp hy with rfl; exact hs
    have huFs : u ⟨{s}, hprop⟩ = s := by
      change ({s} : Finset X).sup' (Finset.singleton_nonempty s) id = s
      rw [Finset.sup'_singleton]; rfl
    rw [← huFs]
    exact hx_lub.1 ⟨⟨{s}, hprop⟩, rfl⟩
  · -- `x` is the least upper bound
    intro y hy
    refine hx_lub.2 ?_
    rintro _ ⟨F, rfl⟩
    exact Finset.sup'_le _ _ (fun s hs => hy (F.prop.1 hs))

end BanachLattice
