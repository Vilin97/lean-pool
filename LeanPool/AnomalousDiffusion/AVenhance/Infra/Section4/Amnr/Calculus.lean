/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Base

/-! Calculus infrastructure for the AMNR tensors. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-! The mixed calculus below keeps spatial and material operations ordered. -/

/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace := ℝ × Vec 2

/-- `none` is the material direction; `some i` is the i-th spatial direction. -/
def amnrDirection (b : AmnrSpace → Vec 2) (d : Option (Fin 2)) (z : AmnrSpace) : AmnrSpace :=
  match d with
  | none => (1, b z)
  | some i => (0, basisVec i)

/-- A directional differential operator on the actual space-time function. -/
def amnrOp (b : AmnrSpace → Vec 2) (d : Option (Fin 2))
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ := fderiv ℝ f z (amnrDirection b d z)

/-- Ordered differential words, with the outermost operator at the head. -/
def amnrWord (b : AmnrSpace → Vec 2) : List (Option (Fin 2)) →
    (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], f => f
  | d :: w, f => amnrOp b d (amnrWord b w f)

theorem Calculus.amnrDirection_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    {n : ℕ} (hb : ContDiffOn ℝ n b U) (d : Option (Fin 2)) :
    ContDiffOn ℝ n (amnrDirection b d) U := by
  cases d with
  | none => exact contDiffOn_const.prodMk hb
  | some i => exact contDiffOn_const

/-- Every word consumes exactly one ordinary derivative per letter. -/
theorem amnrWord_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    (hU : IsOpen U) {N : ℕ} (hb : ContDiffOn ℝ N b U)
    {f : AmnrSpace → ℝ} (hf : ContDiffOn ℝ N f U)
    (w : List (Option (Fin 2))) {n : ℕ} (hn : n + w.length ≤ N) :
    ContDiffOn ℝ n (amnrWord b w f) U := by
  induction w generalizing n with
  | nil => exact hf.of_le (by exact_mod_cast hn)
  | cons d w ih =>
    have hlen : (n + 1) + w.length ≤ N := by simp only [List.length_cons] at hn; omega
    have hw := ih hlen
    have hd := hw.fderiv_of_isOpen hU (show (n : WithTop ℕ∞) + 1 ≤ (n + 1 : ℕ) by norm_cast)
    have hdir := Calculus.amnrDirection_contDiffOn (hb.of_le (by exact_mod_cast (by omega : n ≤
        N))) d
    exact hd.clm_apply hdir

/-- Directional Leibniz rule, with no quantitative hypothesis. -/
theorem amnrOp_mul {b : AmnrSpace → Vec 2} (d : Option (Fin 2))
    {f g : AmnrSpace → ℝ} {z : AmnrSpace}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    amnrOp b d (f * g) z = amnrOp b d f z * g z + f z * amnrOp b d g z := by
  unfold amnrOp
  rw [fderiv_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Directional differentiation commutes with finite sums of differentiable functions. -/
theorem amnrOp_sum {ι : Type*} (S : Finset ι) {b : AmnrSpace → Vec 2}
    (d : Option (Fin 2)) (f : ι → AmnrSpace → ℝ) (z : AmnrSpace)
    (hf : ∀ i ∈ S, DifferentiableAt ℝ (f i) z) :
    amnrOp b d (∑ i ∈ S, f i) z = ∑ i ∈ S, amnrOp b d (f i) z := by
  unfold amnrOp
  rw [fderiv_sum hf]
  simp only [sum_apply]

/-- Ordered Leibniz splittings; each letter goes to exactly one factor. -/
def amnrSplits : List (Option (Fin 2)) → List (List (Option (Fin 2)) × List (Option (Fin 2)))
  | [] => [([], [])]
  | d :: w => (amnrSplits w).flatMap (fun q => [(d :: q.1, q.2), (q.1, d :: q.2)])

theorem amnrSplits_length (w : List (Option (Fin 2))) :
    (amnrSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => simp [amnrSplits]
  | cons d w ih =>
    simp only [amnrSplits, List.length_flatMap, List.length_cons, List.length_nil]
    simp [ih, pow_succ, mul_comm]

theorem amnrSplits_sublist (w : List (Option (Fin 2)))
    (q : List (Option (Fin 2)) × List (Option (Fin 2))) (hq : q ∈ amnrSplits w) :
    q.1.Sublist w ∧ q.2.Sublist w ∧ q.1.length + q.2.length = w.length := by
  induction w generalizing q with
  | nil =>
    have heq : q = ([], []) := by simpa only [amnrSplits, List.mem_singleton] using hq
    subst q
    simp
  | cons d w ih =>
    simp only [amnrSplits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨p, hp, hq⟩ := hq
    obtain ⟨h1, h2, hlen⟩ := ih p hp
    rcases hq with rfl | rfl
    · exact ⟨h1.cons_cons d, h2.cons d, by simp only [List.length_cons]; omega⟩
    · exact ⟨h1.cons d, h2.cons_cons d, by simp only [List.length_cons]; omega⟩

theorem Calculus.amnrList_differentiable (L : List (AmnrSpace → ℝ)) (z : AmnrSpace)
    (h : ∀ f ∈ L, DifferentiableAt ℝ f z) : DifferentiableAt ℝ L.sum z := by
  induction L with
  | nil => exact differentiableAt_const _
  | cons f L ih =>
    exact (h f List.mem_cons_self).add (ih (fun g hg => h g (List.mem_cons_of_mem f hg)))

theorem Calculus.amnrOp_listSum {b : AmnrSpace → Vec 2} (d : Option (Fin 2))
    (L : List (AmnrSpace → ℝ)) (z : AmnrSpace)
    (hL : ∀ f ∈ L, DifferentiableAt ℝ f z) :
    amnrOp b d L.sum z = (L.map (fun f => amnrOp b d f z)).sum := by
  induction L with
  | nil => simp [amnrOp]
  | cons f L ih =>
    have hf := hL f (List.mem_cons_self)
    have htail : ∀ g ∈ L, DifferentiableAt ℝ g z := fun g hg => hL g (List.mem_cons_of_mem f hg)
    have hsum := Calculus.amnrList_differentiable L z htail
    simp only [List.sum_cons, List.map_cons]
    unfold amnrOp at *
    rw [fderiv_add hf hsum, add_apply, ih htail]

/-- The exact mixed Leibniz expansion, derived from directional calculus. -/
theorem amnrWord_mul {U : Set AmnrSpace} (hU : IsOpen U) {N : ℕ}
    {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ N b U)
    {f g : AmnrSpace → ℝ} (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    Set.EqOn (amnrWord b w (f * g))
      (fun z => ((amnrSplits w).map (fun q => amnrWord b q.1 f z * amnrWord b q.2 g z)).sum) U := by
  induction w with
  | nil => intro z hz; simp [amnrWord, amnrSplits]
  | cons d w ih =>
    intro z hz
    have hwN : w.length ≤ N := by simp only [List.length_cons] at hw; omega
    have heq := ih hwN
    let L := (amnrSplits w).map (fun q => fun y => amnrWord b q.1 f y * amnrWord b q.2 g y)
    have hfun : (fun y => ((amnrSplits w).map
        (fun q => amnrWord b q.1 f y * amnrWord b q.2 g y)).sum) = L.sum := by
      funext y
      dsimp [L]
      induction amnrSplits w with
      | nil => rfl
      | cons q Q ih => simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
          (congrArg (fun a => amnrWord b q.1 f y * amnrWord b q.2 g y + a) ih)
    have hnear : amnrWord b w (f * g) =ᶠ[nhds z] L.sum :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).trans (congrFun hfun y))
    have hreg (q) (hq : q ∈ amnrSplits w) :
        DifferentiableAt ℝ (amnrWord b q.1 f) z ∧ DifferentiableAt ℝ (amnrWord b q.2 g) z := by
      have hs := amnrSplits_sublist w q hq
      have h1 := amnrWord_contDiffOn hU hb hf q.1 (n := 1) (by
        simp only [List.length_cons] at hw; have := hs.1.length_le; omega)
      have h2 := amnrWord_contDiffOn hU hb hg q.2 (n := 1) (by
        simp only [List.length_cons] at hw; have := hs.2.1.length_le; omega)
      exact ⟨(h1.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num),
        (h2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)⟩
    have hL : ∀ a ∈ L, DifferentiableAt ℝ a z := by
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact (hreg q hq).1.mul (hreg q hq).2
    change amnrOp b d (amnrWord b w (f * g)) z = _
    unfold amnrOp
    rw [Filter.EventuallyEq.fderiv_eq hnear]
    change amnrOp b d L.sum z = _
    rw [Calculus.amnrOp_listSum d L z hL]
    have hterms : L.map (fun a => amnrOp b d a z) =
        (amnrSplits w).map (fun q => amnrOp b d (amnrWord b q.1 f) z * amnrWord b q.2 g z +
          amnrWord b q.1 f z * amnrOp b d (amnrWord b q.2 g) z) := by
      simp only [L, List.map_map]
      apply List.map_congr_left
      intro q hq
      exact amnrOp_mul d (hreg q hq).1 (hreg q hq).2
    rw [hterms]
    simp only [amnrSplits, List.map_flatMap, List.map_cons, List.map_nil, amnrWord]
    induction amnrSplits w with
    | nil => simp
    | cons q Q ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.sum_append,
        List.sum_nil, add_zero]
      rw [ih]

/-- Radius weights associated with an ordered mixed derivative. -/
def amnrWeight (S H : ℝ) (w : List (Option (Fin 2))) : ℝ :=
  (w.map (fun d => match d with | none => H | some _ => S)).prod

theorem amnrWeight_nonneg {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (w : List (Option (Fin 2))) : 0 ≤ amnrWeight S H w := by
  unfold amnrWeight
  apply List.prod_nonneg
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  cases d <;> assumption

theorem amnrWeight_split (S H : ℝ) (w : List (Option (Fin 2)))
    (q : List (Option (Fin 2)) × List (Option (Fin 2))) (hq : q ∈ amnrSplits w) :
    amnrWeight S H q.1 * amnrWeight S H q.2 = amnrWeight S H w := by
  induction w generalizing q with
  | nil =>
    have heq : q = ([], []) := by simpa only [amnrSplits, List.mem_singleton] using hq
    subst q
    simp [amnrWeight]
  | cons d w ih =>
    simp only [amnrSplits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨p, hp, hq⟩ := hq
    have hh := ih p hp
    rcases hq with rfl | rfl
    · simpa only [amnrWeight, List.map_cons, List.prod_cons, mul_assoc] using congrArg
        (fun a => (match d with | none => H | some _ => S) * a) hh
    · simp only [amnrWeight, List.map_cons, List.prod_cons] at *
      rw [← hh]
      ring

/-- Spatial derivatives outside, material derivatives inside, as in the source. -/
def IsAmnrMixedWord (w : List (Option (Fin 2))) : Prop :=
  w.Pairwise (fun a b => a = none → b = none)

/-- A splitting never changes the order of differentiation on either factor. -/
theorem IsAmnrMixedWord.split {w : List (Option (Fin 2))} (hw : IsAmnrMixedWord w)
    {q : List (Option (Fin 2)) × List (Option (Fin 2))} (hq : q ∈ amnrSplits w) :
    IsAmnrMixedWord q.1 ∧ IsAmnrMixedWord q.2 := by
  have hs := amnrSplits_sublist w q hq
  exact ⟨hw.sublist hs.1, hw.sublist hs.2.1⟩

/-- Material derivatives cost two units in the approved finite-order budget. -/
def amnrBudget (w : List (Option (Fin 2))) : ℕ :=
  (w.map (fun d => match d with | none => 2 | some _ => 1)).sum

theorem amnrBudget_length_le (w : List (Option (Fin 2))) : w.length ≤ amnrBudget w := by
  induction w with
  | nil => simp [amnrBudget]
  | cons d w ih =>
    cases d <;> simp only [amnrBudget, List.map_cons, List.sum_cons, List.length_cons] at * <;>
        omega

theorem amnrBudget_split (w : List (Option (Fin 2)))
    (q : List (Option (Fin 2)) × List (Option (Fin 2))) (hq : q ∈ amnrSplits w) :
    amnrBudget q.1 + amnrBudget q.2 = amnrBudget w := by
  induction w generalizing q with
  | nil =>
    have heq : q = ([], []) := by simpa only [amnrSplits, List.mem_singleton] using hq
    subst q
    simp [amnrBudget]
  | cons d w ih =>
    simp only [amnrSplits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨p, hp, hq⟩ := hq
    have hh := ih p hp
    rcases hq with rfl | rfl <;>
      simp only [amnrBudget, List.map_cons, List.sum_cons] at * <;> omega

/-- The L2 triangle inequality for a list, retaining duplicate Leibniz terms. -/
theorem amnrL2_listSum_le (L : List (AmnrSpace → ℝ)) (μ : Measure AmnrSpace) :
    eLpNorm L.sum 2 μ ≤ (L.map (fun f => eLpNorm f 2 μ)).sum := by
  induction L with
  | nil => simp
  | cons f L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)).trans (add_le_add le_rfl ih)

/-- A bounded smooth multiplier acts on the L2 norm, with an explicit constant. -/
theorem amnrL2_mul_le {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {f g : AmnrSpace → ℝ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ U, |f z| ≤ C) :
    eLpNorm (f * g) 2 μ ≤ ENNReal.ofReal C * eLpNorm g 2 μ := by
  have hm := ((hf.mul hg).aestronglyMeasurable hU.measurableSet (μ := volume)).mono_ac hμ
  have hnorm : ∀ᵐ z ∂μ, ‖(f * g) z‖ ≤ ‖(C • g) z‖ := by
    apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
    intro z hz
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hbound z hz) (abs_nonneg _)
  have hh := eLpNorm_mono_ae hm hnorm (p := 2)
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg hC] at hh
  exact hh

/-- Quantitative mixed Leibniz rule. The two factors consume complementary
budgets, including the two-unit cost of each material derivative. -/
theorem amnrWord_mul_L2_le {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) {S H F G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    (hfb : ∀ v, v.Sublist w → ∀ z ∈ U,
      |amnrWord b v f z| ≤ F * amnrWeight S H v)
    (hgb : ∀ v, v.Sublist w →
      eLpNorm (amnrWord b v g) 2 μ ≤
        ENNReal.ofReal (G * amnrWeight S H v)) :
    eLpNorm (amnrWord b w (f * g)) 2 μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ w.length * F * G * amnrWeight S H w) := by
  have hwN := (amnrBudget_length_le w).trans hw
  let L := (amnrSplits w).map (fun q =>
    fun z => amnrWord b q.1 f z * amnrWord b q.2 g z)
  have heq : amnrWord b w (f * g) =ᵐ[μ] L.sum := by
    apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
    intro z hz
    have hh := amnrWord_mul hU hb hf hg w hwN hz
    change _ = _ at hh
    rw [hh]
    dsimp [L]
    induction amnrSplits w with
    | nil => rfl
    | cons q Q ih => simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
        (congrArg (fun a => amnrWord b q.1 f z * amnrWord b q.2 g z + a) ih)
  rw [eLpNorm_congr_ae heq]
  refine (amnrL2_listSum_le L _).trans ?_
  have hterm (q) (hq : q ∈ amnrSplits w) :
      eLpNorm (fun z => amnrWord b q.1 f z * amnrWord b q.2 g z)
        2 μ ≤ ENNReal.ofReal (F * G * amnrWeight S H w) := by
    have hs := amnrSplits_sublist w q hq
    have hc1 := (amnrWord_contDiffOn hU hb hf q.1 (n := 0)
      (by have := hs.1.length_le; omega)).continuousOn
    have hc2 := (amnrWord_contDiffOn hU hb hg q.2 (n := 0)
      (by have := hs.2.1.length_le; omega)).continuousOn
    have hm := amnrL2_mul_le hU hμ hc1 hc2
      (mul_nonneg hF (amnrWeight_nonneg hS hH q.1)) (hfb q.1 hs.1)
    refine hm.trans ((mul_le_mul_right (hgb q.2 hs.2.1) _).trans_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg hF (amnrWeight_nonneg hS hH q.1))]
    congr 1
    rw [mul_mul_mul_comm, amnrWeight_split S H w q hq]
  have hlist : (L.map (fun a => eLpNorm a 2 μ)).sum ≤
      ((amnrSplits w).map (fun _ => ENNReal.ofReal (F * G * amnrWeight S H w))).sum := by
    simp only [L, List.map_map]
    exact List.sum_le_sum hterm
  refine hlist.trans_eq ?_
  simp only [List.map_const', List.sum_replicate, amnrSplits_length]
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- The joint directional operator is precisely the material operator. -/
theorem amnrOp_material {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {z : AmnrSpace} (hf : DifferentiableAt ℝ f z) :
    amnrOp b none f z = amnrMaterial (fun t x => b (t, x))
      (fun t x => f (t, x)) z.1 z.2 := by
  have ht := (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).hasDerivAt.deriv
  have hx := (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv
  have hvec : b z = ∑ i : Fin 2, b z i • basisVec i := by
    funext i
    simp [basisVec_apply]
  unfold amnrOp amnrDirection amnrMaterial AVenhance.spaceGrad vecDot
  change fderiv ℝ f z (1, b z) = deriv (f ∘ fun s => (s, z.2)) z.1 +
    ∑ i : Fin 2, b z i * fderiv ℝ (f ∘ fun y => (z.1, y)) z.2 (basisVec i)
  rw [ht]
  have hsplit : (1, b z) = ((1, 0) : AmnrSpace) + (0, b z) := by ext <;> simp
  rw [hsplit, map_add]
  congr 1
  conv_lhs => rw [hvec]
  have hpair : ((0, ∑ i : Fin 2, b z i • basisVec i) : AmnrSpace) =
      ∑ i : Fin 2, b z i • ((0, basisVec i) : AmnrSpace) := by
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp [basisVec_apply]
  rw [hpair, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hx]
  rfl

/-- A word depends only on the germ of the differentiated function. -/
theorem amnrWord_congr {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ}
    (hfg : Set.EqOn f g U) (w : List (Option (Fin 2))) :
    Set.EqOn (amnrWord b w f) (amnrWord b w g) U := by
  induction w with
  | nil => exact hfg
  | cons d w ih =>
    intro z hz
    unfold amnrWord amnrOp
    rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hy)).fderiv_eq]

/-- Appending an inner material derivative is exactly the term used by the recursion. -/
theorem amnrWord_append {b : AmnrSpace → Vec 2} (w v : List (Option (Fin 2)))
    (f : AmnrSpace → ℝ) : amnrWord b (w ++ v) f = amnrWord b w (amnrWord b v f) := by
  induction w with
  | nil => rfl
  | cons d w ih => simp only [List.cons_append, amnrWord, ih]

theorem amnrWeight_append (S H : ℝ) (w v : List (Option (Fin 2))) :
    amnrWeight S H (w ++ v) = amnrWeight S H w * amnrWeight S H v := by
  simp [amnrWeight]

theorem amnrBudget_append (w v : List (Option (Fin 2))) :
    amnrBudget (w ++ v) = amnrBudget w + amnrBudget v := by
  simp [amnrBudget]

/-- Mixed words remain mixed when an inner material derivative is appended. -/
theorem IsAmnrMixedWord.material {w : List (Option (Fin 2))} (hw : IsAmnrMixedWord w) :
    IsAmnrMixedWord (w ++ [none]) := by
  exact List.pairwise_append.mpr ⟨hw, by simp, by simp⟩

/-- The Jcut step consumes two units, and every Leibniz factor stays in the
previous level's budget. This check is used at each induction step. -/
theorem amnrLevelBudget {N r : ℕ} {w : List (Option (Fin 2))}
    (hw : amnrBudget w + 2 * (r + 1) ≤ N) :
    amnrBudget (w ++ [none]) + 2 * r ≤ N ∧
      ∀ q ∈ amnrSplits w, amnrBudget q.1 + 2 * r ≤ N ∧
        amnrBudget q.2 + 2 * r ≤ N := by
  constructor
  · rw [amnrBudget_append]
    have hnone : amnrBudget ([none] : List (Option (Fin 2))) = 2 := by rfl
    rw [hnone]
    omega
  · intro q hq
    have hs := amnrBudget_split w q hq
    omega

/-- Differentiating a difference, retaining the actual minus sign. -/
theorem amnrWord_sub {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    Set.EqOn (amnrWord b w (f - g)) (amnrWord b w f - amnrWord b w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons d w ih =>
    have hwN : w.length ≤ N := by simp only [List.length_cons] at hw; omega
    intro z hz
    have hnear := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hwN hy)
    have hf' := (amnrWord_contDiffOn hU hb hf w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    have hg' := (amnrWord_contDiffOn hU hb hg w (n := 1)
      (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds hz)
    unfold amnrWord amnrOp
    rw [hnear.fderiv_eq, fderiv_sub (hf'.differentiableAt (by norm_num))
      (hg'.differentiableAt (by norm_num))]
    rfl

/-- Finite tensor contractions commute with every admissible differential word. -/
theorem amnrWord_sum {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {N : ℕ} (hb : ContDiffOn ℝ N b U)
    {ι : Type*} (s : Finset ι) (f : ι → AmnrSpace → ℝ)
    (hf : ∀ i ∈ s, ContDiffOn ℝ N (f i) U)
    (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    Set.EqOn (amnrWord b w (∑ i ∈ s, f i)) (∑ i ∈ s, amnrWord b w (f i)) U := by
  induction w with
  | nil => intro z _; rfl
  | cons d w ih =>
    have hwN : w.length ≤ N := by simp only [List.length_cons] at hw; omega
    intro z hz
    have hnear := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hwN hy)
    change amnrOp b d (amnrWord b w (∑ i ∈ s, f i)) z = _
    unfold amnrOp
    rw [hnear.fderiv_eq]
    change amnrOp b d (∑ i ∈ s, amnrWord b w (f i)) z = _
    rw [amnrOp_sum]
    · simp only [amnrWord, Finset.sum_apply]
    · intro i hi
      exact ((amnrWord_contDiffOn hU hb (hf i hi) w (n := 1)
        (by simp only [List.length_cons] at hw; omega)).contDiffAt (hU.mem_nhds
            hz)).differentiableAt
          (by norm_num)

end AVenhance.Infra.Section4
