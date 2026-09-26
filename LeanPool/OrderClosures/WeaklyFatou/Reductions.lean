/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.OrderAdherence


/-!
# Weakly Fatou norms

Formalization of the paper's construction of a weakly Fatou Banach lattice norm that is
not equivalent to any lattice norm with the Fatou property.
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-! ## The two reductions -/

section Reductions

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Paper Lemma `lem:order-basic`. -/
theorem iteratedOrderAdherence_mono_and_scale
    {A B : Set X} (_hA : LatticeOrderedAddCommGroup.IsSolid A)
    (_hB : LatticeOrderedAddCommGroup.IsSolid B) {c : ℝ} (hc : 0 < c) :
    (A ⊆ B → ∀ m, iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m) ∧
      (orderAdherence (scaleSet c A) = scaleSet c (orderAdherence A) ∧
        ∀ m, iteratedOrderAdherence (scaleSet c A) m =
          scaleSet c (iteratedOrderAdherence A m)) := by
  have hmono : A ⊆ B → ∀ m,
      iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m := by
    intro hAB m
    induction m with
    | zero => exact hAB
    | succ m ih => exact orderAdherence_mono ih
  have hscale : ∀ C : Set X,
      orderAdherence (scaleSet c C) = scaleSet c (orderAdherence C) := by
    intro C
    apply Set.Subset.antisymm
    · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      refine ⟨c⁻¹ • x, ?_, by simp [smul_smul, hc.ne']⟩
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c⁻¹ • f i, ?_, ?_⟩
      · intro i
        rcases hf i with ⟨a, ha, hfa⟩
        change c⁻¹ • f i ∈ C
        rw [← hfa]
        simpa [smul_smul, hc.ne'] using ha
      · exact hfx.smul c⁻¹
    · rintro x ⟨y, ⟨ι, hpre, hdir, hne, f, hf, hfy⟩, rfl⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c • f i, ?_, hfy.smul c⟩
      exact fun i ↦ ⟨f i, hf i, rfl⟩
  have hiter : ∀ m, iteratedOrderAdherence (scaleSet c A) m =
      scaleSet c (iteratedOrderAdherence A m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simpa only [iteratedOrderAdherence, ih] using
          hscale (iteratedOrderAdherence A m)
  exact ⟨hmono, hscale A, hiter⟩

/-- Paper Lemma `lem:fatou-order`, part (a). -/
theorem weakFatou_iterated_unitBall
    (p : PaperLatticeNorm X) {K : ℝ} (hK : HasWeakFatouProperty p K) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m ⊆
      scaleSet (K ^ m) (unitBallFor p) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK.1
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) ⊆ scaleSet K (unitBallFor p) := by
    rw [orderAdherence_eq_solidOrderAdherence hsolid]
    rintro x ⟨z, hz, hxz⟩
    rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
    let : Nonempty B := hBne.to_subtype
    let : IsDirectedOrder B := hBdir.isDirectedOrder
    let f : B → X := fun b ↦ b.1
    have hfmono : Monotone f := fun _ _ h ↦ h
    have hfrange : Set.range f = B := by
      ext y
      simp [f]
    have hpz : p z ≤ K := by
      have h := hK.2 f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub) 1
        (fun b ↦ hB b.2 |>.1)
      simpa using h
    have hpx : p x ≤ K := (p.solid hxz).trans hpz
    refine ⟨K⁻¹ • x, ?_, by simp [smul_smul, hKpos.ne']⟩
    change p (K⁻¹ • x) ≤ 1
    rw [p.smul, abs_of_pos (inv_pos.mpr hKpos)]
    calc
      K⁻¹ * p x ≤ K⁻¹ * K :=
        mul_le_mul_of_nonneg_left hpx (inv_nonneg.mpr hKpos.le)
      _ = 1 := inv_mul_cancel₀ hKpos.ne'
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro _
      by_cases hm0 : m = 0
      · subst m
        simpa [iteratedOrderAdherence] using hstep
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hpowpos : 0 < K ^ m := pow_pos hKpos m
        have hscale :=
          (iteratedOrderAdherence_mono_and_scale hsolid hsolid hpowpos).2.1
        intro x hx
        change x ∈ orderAdherence (iteratedOrderAdherence (unitBallFor p) m) at hx
        have hxscaled : x ∈ orderAdherence (scaleSet (K ^ m) (unitBallFor p)) :=
          orderAdherence_mono (ih hm1) hx
        rw [hscale] at hxscaled
        rcases hxscaled with ⟨y, hy, hyx⟩
        rcases hstep hy with ⟨z, hz, hzy⟩
        refine ⟨z, hz, ?_⟩
        calc
          K ^ (m + 1) • z = K ^ m • (K • z) := by rw [pow_succ, mul_smul]
          _ = K ^ m • y := congrArg (fun w ↦ K ^ m • w) hzy
          _ = x := hyx

/-- Paper Lemma `lem:fatou-order`, part (b). -/
theorem fatou_iterated_unitBall
    (p : PaperLatticeNorm X) (hp : HasFatouProperty p) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) = unitBallFor p := by
    apply Set.Subset.antisymm
    · rw [orderAdherence_eq_solidOrderAdherence hsolid]
      rintro x ⟨z, hz, hxz⟩
      rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
      let : Nonempty B := hBne.to_subtype
      let : IsDirectedOrder B := hBdir.isDirectedOrder
      let f : B → X := fun b ↦ b.1
      have hfmono : Monotone f := fun _ _ h ↦ h
      have hfrange : Set.range f = B := by
        ext y
        simp [f]
      have hpnorm := hp f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub)
      have hpz : p z ≤ 1 := hpnorm.2 (by
        rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
        exact (hB b.2).1)
      exact (p.solid hxz).trans hpz
    · exact subset_orderAdherence (unitBallFor p)
  have hall : ∀ m, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [iteratedOrderAdherence]
        rw [ih, hstep]
  exact fun m _ ↦ hall m

/-- Weak sequential Nakano constant, Definition 3(a) in the paper. -/
def IsWeakSequentialNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (x : ℕ → X), Monotone x → (∀ m, 0 ≤ x m) →
    BddAbove (Set.range x) → (∀ m, p (x m) ≤ 1) →
      ∀ ε > 0, ∃ y : X, 0 ≤ y ∧ (∀ m, x m ≤ y) ∧ p y ≤ K + ε

/-- Weak Nakano constant, Definition 3(b) in the paper. -/
def IsWeakNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ A : Set X, A ⊆ Ici 0 → DirectedOn (· ≤ ·) A → BddAbove A →
    (∀ x ∈ A, p x ≤ 1) → ∀ ε > 0,
      ∃ y : X, 0 ≤ y ∧ (∀ x ∈ A, x ≤ y) ∧ p y ≤ K + ε

/-- Fremlin's question, as a predicate on a vector lattice: every complete
weakly Fatou lattice norm admits an equivalent Fatou lattice norm. -/
def FremlinProperty : Prop :=
  ∀ p : PaperLatticeNorm X, IsCompleteFor p →
    (∃ K, HasWeakFatouProperty p K) →
      ∃ q : PaperLatticeNorm X, HasFatouProperty q ∧ EquivalentNorms p q

/-- Promotes the sequential weak Nakano estimate to directed sets in a
separable normed lattice; the paper-norm version below reduces to this lemma. -/
theorem weakNakano_of_weakSequentialNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K := by
  refine ⟨hseq.1, ?_⟩
  intro A hApos hAdir hAbdd hAnorm ε hε
  classical
  by_cases hAempty : A = ∅
  · subst A
    refine ⟨0, le_rfl, ?_, ?_⟩
    · simp
    · norm_num
      linarith [hseq.1]
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  let : Nonempty ↥A := ⟨⟨Classical.choose hAne, Classical.choose_spec hAne⟩⟩
  let : TopologicalSpace.SeparableSpace ↥A := inferInstance
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq ↥A
  let join : ↥A → ↥A → ↥A := fun a b ↦
    ⟨Classical.choose (hAdir a.1 a.2 b.1 b.2),
      (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).1⟩
  have hjoin_left (a b : ↥A) : a.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.1
  have hjoin_right (a b : ↥A) : b.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.2
  let z : ℕ → ↥A := fun m ↦
    Nat.rec (d 0) (fun k a ↦ join a (d (k + 1))) m
  have hz_succ (m : ℕ) : z (m + 1) = join (z m) (d (m + 1)) := by
    simp [z]
  have hzmono : Monotone (fun m ↦ (z m).1) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [hz_succ]
    exact hjoin_left _ _
  have hd_le_z : ∀ m, (d m).1 ≤ (z m).1 := by
    intro m
    cases m with
    | zero => simp [z]
    | succ m =>
        rw [hz_succ]
        exact hjoin_right _ _
  have hzpos : ∀ m, 0 ≤ (z m).1 := fun m ↦ hApos (z m).2
  have hzbdd : BddAbove (Set.range fun m ↦ (z m).1) := by
    rcases hAbdd with ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨m, rfl⟩; exact hb (z m).2⟩
  have hznorm : ∀ m, ‖(z m).1‖ ≤ 1 := fun m ↦ hAnorm _ (z m).2
  obtain ⟨y, hypos, hyupper, hynorm⟩ :=
    hseq.2 (fun m ↦ (z m).1) hzmono hzpos hzbdd hznorm ε hε
  refine ⟨y, hypos, ?_, hynorm⟩
  have hd_upper : ∀ m, (d m).1 ≤ y :=
    fun m ↦ (hd_le_z m).trans (hyupper m)
  have hclosed : IsClosed {a : ↥A | a.1 ≤ y} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hclosure : closure (Set.range d) ⊆ {a : ↥A | a.1 ≤ y} := by
    apply closure_minimal
    · rintro _ ⟨m, rfl⟩
      exact hd_upper m
    · exact hclosed
  intro x hx
  let xA : ↥A := ⟨x, hx⟩
  exact hclosure (by rw [hdense.closure_eq]; exact Set.mem_univ xA)

/-- Converts the directed weak Nakano estimate into the weak Fatou inequality
for an ambient norm; reused after transporting a paper lattice norm. -/
theorem weakFatou_of_weakNakano_norm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) norm K) :
    HasWeakFatouProperty (norm : Y → ℝ) K := by
  refine ⟨hNak.1, ?_⟩
  intro ι _ _ _ f x hfmono hfpos hflub c hfc
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hc : 0 ≤ c := (norm_nonneg (f i₀)).trans (hfc i₀)
  by_cases hc0 : c = 0
  · subst c
    have hfzero : ∀ i, f i = 0 := by
      intro i
      exact norm_eq_zero.mp (le_antisymm (hfc i) (norm_nonneg _))
    have hxzero : x = 0 := by
      apply le_antisymm
      · apply hflub.2
        rintro _ ⟨i, rfl⟩
        simp [hfzero i]
      · simpa [hfzero i₀] using hflub.1 ⟨i₀, rfl⟩
    simp [hxzero]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let A : Set Y := Set.range fun i ↦ c⁻¹ • f i
  have hApos : A ⊆ Set.Ici 0 := by
    rintro _ ⟨i, rfl⟩
    exact smul_nonneg (inv_nonneg.mpr hc) (hfpos i)
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨c⁻¹ • f k, ⟨k, rfl⟩, ?_, ?_⟩
    · exact smul_le_smul_of_nonneg_left (hfmono hik) (inv_nonneg.mpr hc)
    · exact smul_le_smul_of_nonneg_left (hfmono hjk) (inv_nonneg.mpr hc)
  have hAbdd : BddAbove A := by
    refine ⟨c⁻¹ • x, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact smul_le_smul_of_nonneg_left (hflub.1 ⟨i, rfl⟩) (inv_nonneg.mpr hc)
  have hAnorm : ∀ z ∈ A, ‖z‖ ≤ 1 := by
    rintro _ ⟨i, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    have hi := hfc i
    rw [inv_mul_le_one₀ hcpos]
    exact hi
  obtain ⟨y, hypos, hyupper, hynorm⟩ :=
    hNak.2 A hApos hAdir hAbdd hAnorm (δ / c) (div_pos hδ hcpos)
  have hxy : x ≤ c • y := by
    apply hflub.2
    rintro _ ⟨i, rfl⟩
    have hi := hyupper (c⁻¹ • f i) ⟨i, rfl⟩
    have := smul_le_smul_of_nonneg_left hi hc
    simpa [smul_smul, hc0] using this
  have hxpos : 0 ≤ x := (hfpos i₀).trans (hflub.1 ⟨i₀, rfl⟩)
  have hcyp : 0 ≤ c • y := smul_nonneg hc hypos
  have hnormxy : ‖x‖ ≤ ‖c • y‖ := by
    apply norm_le_norm_of_abs_le_abs
    simpa [abs_of_nonneg hxpos, abs_of_nonneg hcyp] using hxy
  calc
    ‖x‖ ≤ ‖c • y‖ := hnormxy
    _ = c * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    _ ≤ c * (K + δ / c) := mul_le_mul_of_nonneg_left hynorm hc
    _ = K * c + δ := by field_simp

/-- Paper Proposition `prop:separable-reduction`. -/
theorem separable_weakSequentialNakano_implies_weakNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (_hK : 1 ≤ K)
    (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K ∧
      HasWeakFatouProperty (norm : Y → ℝ) K := by
  have hNak := weakNakano_of_weakSequentialNakano hseq
  exact ⟨hNak, weakFatou_of_weakNakano_norm hNak⟩

/-- Extends the separable sequential-to-directed reduction to an arbitrary
`PaperLatticeNorm`; used to prove `component_weakFatou`. -/
theorem weakNakano_of_weakSequentialNakano_p
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    (p : PaperLatticeNorm Y) {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) p K) :
    IsWeakNakanoConstant (X := Y) p K := by
  refine ⟨hseq.1, ?_⟩
  intro A hApos hAdir hAbdd hAp ε hε
  classical
  by_cases hAempty : A = ∅
  · subst A
    refine ⟨0, le_rfl, by simp, ?_⟩
    rw [show p 0 = 0 from p.eq_zero_iff 0 |>.2 rfl]
    linarith [hseq.1]
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  let : Nonempty ↥A := ⟨⟨Classical.choose hAne, Classical.choose_spec hAne⟩⟩
  let : TopologicalSpace.SeparableSpace ↥A := inferInstance
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq ↥A
  let join : ↥A → ↥A → ↥A := fun a b ↦
    ⟨Classical.choose (hAdir a.1 a.2 b.1 b.2),
      (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).1⟩
  have hjoin_left (a b : ↥A) : a.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.1
  have hjoin_right (a b : ↥A) : b.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.2
  let z : ℕ → ↥A := fun m ↦
    Nat.rec (d 0) (fun k a ↦ join a (d (k + 1))) m
  have hz_succ (m : ℕ) : z (m + 1) = join (z m) (d (m + 1)) := by simp [z]
  have hzmono : Monotone (fun m ↦ (z m).1) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [hz_succ]
    exact hjoin_left _ _
  have hd_le_z : ∀ m, (d m).1 ≤ (z m).1 := by
    intro m
    cases m with
    | zero => simp [z]
    | succ m => rw [hz_succ]; exact hjoin_right _ _
  have hzpos : ∀ m, 0 ≤ (z m).1 := fun m ↦ hApos (z m).2
  have hzbdd : BddAbove (Set.range fun m ↦ (z m).1) := by
    rcases hAbdd with ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨m, rfl⟩; exact hb (z m).2⟩
  have hzp : ∀ m, p (z m).1 ≤ 1 := fun m ↦ hAp _ (z m).2
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hseq.2 (fun m ↦ (z m).1) hzmono hzpos hzbdd hzp ε hε
  refine ⟨y, hypos, ?_, hyp⟩
  have hd_upper : ∀ m, (d m).1 ≤ y := fun m ↦ (hd_le_z m).trans (hyupper m)
  have hclosed : IsClosed {a : ↥A | a.1 ≤ y} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hclosure : closure (Set.range d) ⊆ {a : ↥A | a.1 ≤ y} := by
    apply closure_minimal
    · rintro _ ⟨m, rfl⟩
      exact hd_upper m
    · exact hclosed
  intro q hq
  exact hclosure (by rw [hdense.closure_eq]; exact Set.mem_univ ⟨q, hq⟩)

/-- Extends the weak-Nakano-to-weak-Fatou implication to a
`PaperLatticeNorm`; used for the component norm in `component_weakFatou`. -/
theorem weakFatou_of_weakNakano_p
    {Y : Type u} [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (p : PaperLatticeNorm Y) {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) p K) :
    HasWeakFatouProperty p K := by
  refine ⟨hNak.1, ?_⟩
  intro ι _ _ _ f x hfmono hfpos hflub c hfc
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hc : 0 ≤ c := (p.nonneg (f i₀)).trans (hfc i₀)
  by_cases hc0 : c = 0
  · subst c
    have hfzero : ∀ i, f i = 0 := by
      intro i
      apply p.eq_zero_iff (f i) |>.1
      exact le_antisymm (hfc i) (p.nonneg _)
    have hxzero : x = 0 := by
      apply le_antisymm
      · apply hflub.2
        rintro _ ⟨i, rfl⟩
        simp [hfzero i]
      · simpa [hfzero i₀] using hflub.1 ⟨i₀, rfl⟩
    rw [hxzero]
    rw [p.eq_zero_iff 0 |>.2 rfl]
    simp
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let A : Set Y := Set.range fun i ↦ c⁻¹ • f i
  have hApos : A ⊆ Set.Ici 0 := by
    rintro _ ⟨i, rfl⟩
    exact smul_nonneg (inv_nonneg.mpr hc) (hfpos i)
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨c⁻¹ • f k, ⟨k, rfl⟩, ?_, ?_⟩
    · exact smul_le_smul_of_nonneg_left (hfmono hik) (inv_nonneg.mpr hc)
    · exact smul_le_smul_of_nonneg_left (hfmono hjk) (inv_nonneg.mpr hc)
  have hAbdd : BddAbove A := by
    refine ⟨c⁻¹ • x, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact smul_le_smul_of_nonneg_left (hflub.1 ⟨i, rfl⟩) (inv_nonneg.mpr hc)
  have hAp : ∀ z ∈ A, p z ≤ 1 := by
    rintro _ ⟨i, rfl⟩
    rw [p.smul, abs_of_pos (inv_pos.mpr hcpos), inv_mul_le_one₀ hcpos]
    exact hfc i
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hNak.2 A hApos hAdir hAbdd hAp (δ / c) (div_pos hδ hcpos)
  have hxy : x ≤ c • y := by
    apply hflub.2
    rintro _ ⟨i, rfl⟩
    have hi := hyupper (c⁻¹ • f i) ⟨i, rfl⟩
    have := smul_le_smul_of_nonneg_left hi hc
    simpa [smul_smul, hc0] using this
  have hxpos : 0 ≤ x := (hfpos i₀).trans (hflub.1 ⟨i₀, rfl⟩)
  have hcyp : 0 ≤ c • y := smul_nonneg hc hypos
  have hpxy : p x ≤ p (c • y) := by
    apply p.solid
    simpa [abs_of_nonneg hxpos, abs_of_nonneg hcyp] using hxy
  calc
    p x ≤ p (c • y) := hpxy
    _ = c * p y := by rw [p.smul, abs_of_pos hcpos]
    _ ≤ c * (K + δ / c) := mul_le_mul_of_nonneg_left hyp hc
    _ = K * c + δ := by field_simp

end Reductions

end OrderClosures
