/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

/-!
# LeanPool.Polylean.Complexes.GraphPaths
-/

namespace LeanPool.Polylean

/-- A graph with directed edges, distinguished null edge, and edge reversal. -/
structure Graph (V : Type) (E : Type) where
  /-- The distinguished null edge. -/
  null : E
  /-- The initial vertex of an edge. -/
  init : E → V
  /-- The reverse of an edge. -/
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e : E, bar e ≠ e

variable {V : Type} {E : Type} {x₁ x₂ : V}


/-- The terminal vertex of an edge, defined as the initial vertex of its reverse. -/
@[inline] def term (graph : Graph V E) : E → V :=
  fun e => graph.init (graph.bar e)

/-- Edge paths in a graph, indexed by their initial and terminal vertices. -/
inductive EdgePath (graph : Graph V E) : V → V → Type where
  | single : (x : V) → EdgePath graph x x
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →
        EdgePath graph y z → EdgePath graph x z

namespace EdgePath

/-- The number of edges in an edge path. -/
def length {graph : Graph V E} {x y : V} : EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1

end EdgePath

/-- proves that bar is an involution -/
theorem bar_involution {G : Graph V E} : (ex : E) → G.bar (G.bar ex) = ex := by
  intro ex
  apply congr G.barInv (Eq.refl ex)


open EdgePath

/-- concatenates two edgepaths -/
def multiply {G : Graph V E} {x y z : V} :
    (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) := by
  intro p q
  match p with
  | single x => exact q
  | cons ex h1 h2 exy => exact (cons ex h1 h2 (multiply exy q))


/-- proves that the endpoint of the reverse of an edge is the start point of the edge -/
theorem term_bar_equals_init {G : Graph V E} {x : V} {e : E} :
    G.init e = x → (term G (G.bar e) = x) := by
  intro h
  have h₂ : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init (bar_involution e)
  apply Eq.trans h₂ h

/-- proves that initial vertex of reversed edge is the terminal vertex of the original edge -/
theorem init_bar_equals_term {G : Graph V E} {x : V} {e : E} :
    (term G e = x) → G.init (G.bar e) = x := id

/-- proves associativity of path multiplication -/
theorem mult_assoc {G : Graph V E}
    (p : EdgePath G w x) (q : EdgePath G x y) (r : EdgePath G y z) :
      (multiply (multiply p q) r) = (multiply p (multiply q r)) := by
  induction p with
  | single w => simp[multiply]
  | cons ex h1 h2 exy ih => simp[multiply, ih]

/-- proves that "single x" is an identity element for multiplication -/
theorem mult_const {G : Graph V E} (p : EdgePath G x y) :
      (multiply p (single y)) = p := by
      induction p with
      | single x => simp [multiply]
      | cons ex h1 h2 exy ih => simp[multiply, ih]

/-- reverses an edgepath -/
def inverse {G : Graph V E} {x y : V} : (EdgePath G x y) → (EdgePath G y x)
| single x => single x
| cons ex h₁ h₂ exy =>
  multiply (inverse exy) (cons (G.bar ex) h₂ (term_bar_equals_init h₁) (single x))


/-- defines an edgepath with a single edge -/
def basicpath {G : Graph V E} (x : V) (ex : E)
    (h₁ : G.init ex = x) (h₂ : term G ex = y) : EdgePath G x y :=
  cons ex h₁ h₂ (single y)

/-- proves that multiplication with a basicpath gives inductive definition of edgepath -/
theorem basicpath_mult {G : Graph V E} {x y z : V} (ex : E)
    (h₁ : G.init ex = x) (h₂ : term G ex = y) (exy : EdgePath G y z) :
    multiply (basicpath x ex h₁ h₂) exy = cons ex h₁ h₂ exy := by
  simp[basicpath, multiply]

/-- defines inverse in terms of basicpath -/
theorem inverse_lemma {G : Graph V E} {x y z : V} (ex : E)
    (h₁ : G.init ex = x) (h₂ : term G ex = y) (exy : EdgePath G y z) :
    inverse (cons ex h₁ h₂ exy) =
      multiply (inverse exy) (basicpath y (G.bar ex) h₂ (term_bar_equals_init h₁)) := by
  rfl


/-- proves the basic relation between inverse and multiply -/
theorem inverse_mult {G : Graph V E} (x y z : V) (p : EdgePath G x y) (q : EdgePath G y z) :
      inverse (multiply p q) = multiply (inverse q) (inverse p) := by
      induction p with
      | single x =>
            have p₁ : multiply (single x) q = q := by rfl
            rw[p₁]
            have p₂ : @inverse V E G x x (single x) = single x := by simp[inverse]
            rw[p₂]
            rw[mult_const (inverse q)]
      | cons ex t₁ t₂ exy ih =>
          have p₃ :
              multiply (cons ex t₁ t₂ exy) q = cons ex t₁ t₂ (multiply exy q) := by
            simp [multiply]
          rw[p₃]
          have p₄ :
              inverse (cons ex t₁ t₂ exy) =
                multiply (inverse exy)
                  (basicpath _ (G.bar ex) t₂ (term_bar_equals_init t₁)) := by
            simp[inverse_lemma]
          rw[p₄]
          have p₅ : multiply (inverse q) (inverse exy) = inverse (multiply exy q) := by
            simp[ih q]
          let p₆ := inverse_lemma ex t₁ t₂ (multiply exy q)
          rw[p₆]
          simp[Eq.symm (p₅), mult_assoc]


/-- proves that inverse is an involution on paths -/
theorem inverse_involution {G : Graph V E} {x y : V} (p : EdgePath G x y) :
    inverse (inverse p) = p := by
  induction p with
  | single x => rfl
  | cons ex h₁ h₂ exy ih =>
    have p₁ :
        inverse (cons ex h₁ h₂ exy) =
          multiply (inverse exy) (inverse (basicpath _ ex h₁ h₂)) := by
      rfl
    rw[p₁]
    let k := inverse_mult _ _ _ (inverse exy)  (inverse (basicpath _ ex h₁ h₂))
    rw[k]
    have p₂ : inverse (inverse (basicpath _ ex h₁ h₂)) = basicpath _ ex h₁ h₂ := by
      simp[basicpath, inverse]
      simp only [bar_involution ex, inverse, multiply]
    rw[p₂]
    simp[basicpath_mult ex h₁ h₂ exy, ih]



/-- helper function for reducePath, that reduces the first two edges of the path -/
def reducePathAux [DecidableEq V] [DecidableEq E] {G : Graph V E} {x y z : V}
    (ex : E) (h₁ : G.init ex = x) (h₂ : term G ex = y) (exy : EdgePath G y z) :
    { rp : EdgePath G x z // rp.length ≤ (cons ex h₁ h₂ exy).length} := by
  cases exy with
  | single x => exact ⟨cons ex h₁ h₂ (single y), by simp⟩
  | cons ey h₃ h₄ eyz =>
    apply
    if c : (x = term G ey) ∧ (ey = G.bar ex) then
    ⟨ Eq.symm (Eq.trans (And.left c) h₄) ▸ eyz, by
      have h₅ : (Eq.symm (Eq.trans (And.left c) h₄) ▸ eyz).length = eyz.length := by
        let ih := Eq.symm (Eq.trans (And.left c) h₄)
        cases ih with
        | refl => rfl
      simp [EdgePath.length, h₅,
        Nat.le_trans (Nat.le_succ (length eyz)) (Nat.le_succ (length eyz + 1))]
    ⟩
    else
    ⟨ cons ex h₁ h₂ (cons ey h₃ h₄ eyz), by apply Nat.le_refl⟩


/-- reduces given path such that no two consecutive edges are inverses of each other -/
def reducePath [DecidableEq V] [DecidableEq E] {G : Graph V E} : (p : EdgePath G x y ) →
  {rp : EdgePath G x y // rp.length ≤ p.length}
| single x => ⟨single x, by simp⟩
| cons ex h₁ h₂ ey'y =>
  let ⟨ey'z, ih1⟩ := reducePath ey'y
  let ⟨ ez, ih⟩ := reducePathAux ex h₁ h₂ ey'z
  ⟨ ez , by
          have : length (cons ex h₁ h₂ ey'z) = length ey'z + 1 := by simp[length]
          let k := this ▸ ih
          have pr : length ey'z + 1 ≤ length ey'y + 1 := by apply Nat.succ_le_succ ih1
          simp[length, Nat.le_trans k pr] ⟩
  termination_by p => p.length
  decreasing_by
  simp[EdgePath.length]


/-- defines moves allowing homotopy of edgepaths -/
inductive basicht {G : Graph V E} : EdgePath G x y → EdgePath G x y → Prop where
  | consht : (x : V) → (basicht (single x) (single x)) -- constant homotopy
  | cancel :
      (ex ex' : E) → {x w y : V} → (p : EdgePath G x y) →
      (h : G.init ex = x) → (h' : term G ex = w) → (t : G.bar ex = ex') →
      basicht p
        (cons ex h h' (cons ex' (t ▸ init_bar_equals_term h')
          (t ▸ term_bar_equals_init h) p))
  | mult : {x y z : V} → {p q : EdgePath G y z} →   -- adding an edge to homotopic paths
          basicht p q → (ex : E) → (h' : G.init ex = x) → (h : term G ex = y) →
          basicht (cons ex h' h p) (cons ex h' h q)


/-- The set of homotopy classes of edge paths from `x` to `y`. -/
def ht (G : Graph V E) (x y : V) := Quot (@basicht V E G x y)

/-- The homotopy class of an edge path. -/
def htclass {G : Graph V E} {x y : V} (p : EdgePath G x y) : ht G x y :=
  Quot.mk (@basicht V E G x y) p

/-- Homotopy of edge paths as equality of their quotient classes. -/
def homotopy {G : Graph V E} {x y : V} (p' q' : EdgePath G x y) : Prop :=
  htclass p' = htclass q'


/-- proves that homotopy is a transitive relation -/
theorem homotopy_trans {G : Graph V E} {x y : V} (p q r : EdgePath G x y) :
    homotopy p q → homotopy q r → homotopy p r := Eq.trans


/-- proves that homotopy is preserved by multiplying an edge to the left -/
theorem homotopy_left_mult_edge {G : Graph V E} {x y z : V} :
    (p q : EdgePath G y z) → homotopy p q → (ex : E) → (h1 : G.init ex = x) →
    (h : term G ex = y) → homotopy (cons ex h1 h p) (cons ex h1 h q) := by
  intro p q h ex h1 h2
  let func (r : EdgePath G y z) : ht G x z := htclass (cons ex h1 h2 r)
  have g : (r₁ r₂ : EdgePath G y z) →  basicht r₁ r₂ → func r₁ = func r₂ := by
     intro r₁ r₂ h₁
     exact Quot.sound (basicht.mult h₁ ex h1 h2)
  change Quot.lift func g (htclass p) = Quot.lift func g (htclass q)
  let k := Quot.lift func g
  apply congrArg k h


/-- proves that homotopy is left multiplicative -/
theorem homotopy_left_mult {G : Graph V E} {x y z : V}
    (p1 p2 : EdgePath G y z) (q : EdgePath G x y) (h : homotopy p1 p2) :
         (homotopy (multiply q p1) (multiply q p2)) := by
         induction q with
        | single w  =>
          simp [multiply, h]
        | cons ex h1 h2 exy ih =>
          let c := ih p1 p2 h
          have t₁ :
              multiply (cons ex h1 h2 exy) p1 = cons ex h1 h2 (multiply exy p1) := by
            simp [multiply]
          have t₂ :
              multiply (cons ex h1 h2 exy) p2 = cons ex h1 h2 (multiply exy p2) := by
            simp [multiply]
          rw[t₁, t₂]
          simp[homotopy_left_mult_edge, c]


/-- proves that homotopy is reflexive -/
theorem homotopy_rfl {G : Graph V E} {x y : V} (p : EdgePath G x y) : homotopy p p := by rfl


/-- proves that path is homotopic to itself after appending cancelling pair of edges at its end -/
theorem induct_homotopy_inverse_cancel {G : Graph V E} (ey ey' : E) {x w y : V}
    (p : EdgePath G x y) (h₁ : G.init ey = y) (h₂ : term G ey = w)
    (t : G.bar ey = ey') (h₃ : G.init ey' = w) (h₄ : term G ey' = y) :
           homotopy p (multiply p (cons ey h₁ h₂ (cons ey' h₃ h₄ (single y)) )) := by
           induction p with
           | single x =>
             simp [multiply, homotopy, htclass,
               Quot.sound (basicht.cancel ey ey' (single x) h₁ h₂ t)]
           | cons ex t₁ t₂ exy ih =>
            let x := ih h₁ h₄
            have p₁ :
                homotopy (cons ex t₁ t₂ exy)
                  (cons ex t₁ t₂
                    (multiply exy (cons ey h₁ h₂ (cons ey' h₃ h₄ (single _))))) := by
              simp[homotopy_left_mult_edge _ _ x ex t₁ t₂]
            have :
                cons ex t₁ t₂
                    (multiply exy (cons ey h₁ h₂ (cons ey' h₃ h₄ (single _)))) =
                  multiply (cons ex t₁ t₂ exy)
                    (cons ey h₁ h₂ (cons ey' h₃ h₄ (single _))) := by
              simp[multiply]
            exact this ▸ p₁


/-- proves that a pair of paths remains homotopic after appending a single edge at their ends -/
theorem induct_homotopy_inverse_mult {G : Graph V E} {x y z : V}
    (p q : EdgePath G x y) (ey : E) (h₁ : G.init ey = y) (h₂ : term G ey = z) :
    homotopy p q →
      homotopy (multiply p (basicpath y ey h₁ h₂))
        (multiply q (basicpath y ey h₁ h₂)) := by
    intro h
    let func : EdgePath G x y → ht G x z := by
      intro p
      exact htclass (multiply p (basicpath y ey h₁ h₂))
    have g : (s₁ s₂ : EdgePath G x y) → (basicht s₁ s₂) → func s₁ = func s₂ := by
      intro s₁ s₂ ht
      induction ht with
      | consht x => simp
      | cancel ex ex' r t₁ t₂ t₃ =>
        let x := basicht.cancel ex ex' (multiply r (basicpath _ ey h₁ h₂)) t₁ t₂ t₃
        exact Quot.sound x
      | @mult _ _ _ p₁ p₂ b ex t₁ t₂ ih =>
        let x := homotopy_left_mult_edge _ _ (ih p₁ p₂ h₁ (Quot.sound b)) ex t₁ t₂
        exact x
    change Quot.lift func g (htclass p) = Quot.lift func g (htclass q)
    let k := Quot.lift func g
    apply congrArg k h


/-- proves that homotopy of paths implies homotopy of their inverses -/
theorem homotopy_inverse {G : Graph V E} {x y : V}
    (p₁ p₂ : EdgePath G x y) (q₁ q₂ : EdgePath G y x)
    (h₁ : q₁ = inverse p₁) (h₂ : q₂ = inverse p₂) :
    homotopy p₁ p₂ → homotopy q₁ q₂ := by
  intro h₀
  let func : EdgePath G x y → ht G y x := by
    intro p
    exact htclass (inverse p)
  have g : (s₁ s₂ : EdgePath G x y) → (h : basicht s₁ s₂) →
      homotopy (inverse s₁) (inverse s₂) := by
      intro s₁ s₂ h
      induction h with
        | consht x => simp[inverse, homotopy_rfl]
        | cancel ex ex' p t₁ t₂ t₃ =>
          simpa [inverse, mult_assoc, multiply] using
            induct_homotopy_inverse_cancel (G.bar ex') (G.bar ex) (inverse p)
              (by rw[← t₃]; rw[bar_involution ex]; apply t₁)
              (by rw[← t₃]; rw[(bar_involution ex)]; apply t₂)
              (by rw[bar_involution ex']; apply (Eq.symm t₃))
              (init_bar_equals_term t₂) (term_bar_equals_init t₁)
        | @mult _ _ _ s₁ s₂ b ex t₁ t₂ ih =>
          let c := ih s₁ s₂ (inverse s₁) (inverse s₂) rfl rfl (Quot.sound b)
          let k :=
            induct_homotopy_inverse_mult (inverse s₁) (inverse s₂) (G.bar ex) t₂
              (term_bar_equals_init t₁) c
          simpa [homotopy, inverse, basicpath] using k
  let k₂ := Quot.lift func g
  rw [h₁, h₂]
  exact congrArg k₂ h₀


/-- homotopy_inverse with lesser arguments -/
theorem homotopy_inverse_quick {G : Graph V E} {x y : V} {p₁ p₂ : EdgePath G x y} :
    homotopy p₁ p₂ → homotopy (inverse p₁) (inverse p₂) := by
  apply homotopy_inverse p₁ p₂ (inverse p₁) (inverse p₂) rfl rfl


/-- proves that homotopy is right multiplicative -/
theorem homotopy_right_mult {G : Graph V E} {x y z : V}
    (p₁ p₂ : EdgePath G x y) (q : EdgePath G y z) (h : homotopy p₁ p₂) :
         (homotopy (multiply p₁ q) (multiply p₂ q)) := by
         have r₁ : homotopy (inverse p₁) (inverse p₂) := by apply homotopy_inverse_quick h
         have r₂ :
             homotopy (multiply (inverse q) (inverse p₁))
               (multiply (inverse q) (inverse p₂)) := by
           apply homotopy_left_mult
           apply r₁
         have r₃ :
             homotopy (inverse (multiply (inverse q) (inverse p₁)))
               (inverse (multiply (inverse q) (inverse p₂))) := by
           apply homotopy_inverse_quick r₂
         let s₁ := inverse_mult x y z p₁ q
         let s₂ := inverse_involution (multiply p₁ q)
         let s₃ := Eq.trans (Eq.symm s₂) (congrArg inverse s₁)
         let t₁ := inverse_mult x y z p₂ q
         let t₂ := inverse_involution (multiply p₂ q)
         let t₃ := Eq.trans (Eq.symm t₂) (congrArg inverse t₁)
         apply s₃ ▸ t₃ ▸ r₃


/-- defines multiplication of homotopy class with a path to its left -/
def homotopyLeftMultiplication {G : Graph V E} {x y z : V}
    (p₁ : EdgePath G x y) : ht G y z →  ht G x z := by
  let func : EdgePath G y z → ht G x z := by
    intro p
    exact htclass (multiply p₁ p)
  have g : (q₁ q₂ : EdgePath G y z) → basicht q₁ q₂ → func q₁ = func q₂ := by
          intro q₁ q₂ h
          have h' : homotopy q₁ q₂ := by simp[homotopy, htclass, Quot.sound h ]
          apply homotopy_left_mult q₁ q₂ p₁ h'
  apply Quot.lift func g


/-- proves that the multiplication defined above equals homotopy class of multiplied paths -/
theorem homotopy_left_multiplication_class {G : Graph V E} {x y z : V}
    (p₁ : EdgePath G x y) (p₂ : EdgePath G y z) :
    homotopyLeftMultiplication p₁ (htclass p₂) = htclass (multiply p₁ p₂) := by
  simp[htclass, homotopyLeftMultiplication]


/-- defines multiplication of homotopy -/
def homotopyMultiplication : ht G x y → ht G y z → ht G x z := by
  intro p₁ p₂
  let func (p : EdgePath G x y) : ht G x z := homotopyLeftMultiplication p p₂
  have g : (q₁ q₂ : EdgePath G x y) → basicht q₁ q₂ → func q₁ = func q₂  := by
      intro q₁ q₂ h
      let crop (p : ht G y z) : Prop :=
        homotopyLeftMultiplication q₁ p = homotopyLeftMultiplication q₂ p
      have g' : (p : ht G y z) → crop p := by
        intro p
        have g'' : (p' : EdgePath G y z) → crop (htclass p') := by
          intro p'
          have h' : homotopy q₁ q₂ := by simp[homotopy, htclass, Quot.sound h]
          have : htclass (multiply q₁ p') = htclass (multiply q₂ p') := by
            exact homotopy_right_mult q₁ q₂ p' h'
          exact this
        apply Quot.ind g''
      let hh := g' p₂
      exact hh
  let k := (Quot.lift (fun x => func x) g)
  apply k p₁


/-- Multiplication of homotopy classes of composable edge paths. -/
infixl: 65 " # " => homotopyMultiplication


/-- proves that # is associative up to multiplication by a pair of paths and one homotopy class -/
theorem homotopy_mult_path_path_assoc {G : Graph V E} {w x y z : V}
    (p : EdgePath G w x) (q : EdgePath G x y) :
    (r : ht G y z) → (htclass (multiply p q)) # r = (htclass p) # ((htclass q) # r) := by
  apply Quot.ind
  intro b
  change
    homotopyLeftMultiplication (multiply p q) (Quot.mk basicht b) =
      homotopyLeftMultiplication p (homotopyLeftMultiplication q (Quot.mk basicht b))
  have p₁ :
      homotopyLeftMultiplication (multiply p q) (Quot.mk basicht b) =
        htclass (multiply (multiply p q) b) := by
    rfl
  have p₂ :
      homotopyLeftMultiplication q (Quot.mk basicht b) = htclass (multiply q b) := by
    rfl
  have p₃ :
      homotopyLeftMultiplication p (homotopyLeftMultiplication q (Quot.mk basicht b)) =
        htclass (multiply p (multiply q b)) := by
    rw[p₂]
    rfl
  rw[p₁,p₃]
  simp[mult_assoc]


/-- proves that # is associative up to multiplication by one path and a pair of homotopy classes -/
theorem homotopy_mult_path_assoc {G : Graph V E} {w x y z : V}
    (p : EdgePath G w x) (r : ht G y z) :
    (q : ht G x y) → (htclass p # q) # r = (htclass p) # (q # r) := by
  apply Quot.ind
  intro a
  change Quot.mk basicht p # Quot.mk basicht a # r = Quot.mk basicht p # (Quot.mk basicht a # r)
  have p₁ : Quot.mk basicht p # Quot.mk basicht a = htclass (multiply p a) := by rfl
  rw[p₁]
  apply homotopy_mult_path_path_assoc p a r

/-- proves that # is associative on homotopy classes -/
theorem homotopy_mult_assoc {G : Graph V E} {w x y z : V}
    (b : ht G x y) (c : ht G y z) :
    (a : ht G w x) → ((a # b) # c) = (a # (b # c)) := by
  apply Quot.ind
  intro a
  apply homotopy_mult_path_assoc a c b



/-- proves that reducePathAux preserves the homotopy class -/
theorem homotopy_reducePathAux [DecidableEq V] [DecidableEq E] {G : Graph V E}
    {x y z : V} (ex : E) (h₁ : G.init ex = x) (h₂ : term G ex = y)
    (exy : EdgePath G y z) : homotopy (cons ex h₁ h₂ exy) (reducePathAux ex h₁ h₂ exy) := by
  change
    Quot.mk basicht (cons ex h₁ h₂ exy) =
      Quot.mk basicht (reducePathAux ex h₁ h₂ exy).val
  cases exy with
  | single y =>
      have : reducePathAux ex h₁ h₂ (single y) = cons ex h₁ h₂ (single y) := by rfl
      rfl
  | cons ey h₃ h₄ eyz =>
    by_cases c : (x = term G ey) ∧ (ey = G.bar (ex))
    · let ih := Eq.symm (Eq.trans (And.left c) h₄)
      cases ih with
      |refl =>
          have : basicht (ih ▸ eyz)  (cons ex h₁ h₂ (cons ey h₃ h₄ eyz))  := by
            let j := @basicht.cancel V E G ex ey x y _ (ih ▸ eyz) h₁ h₂ (Eq.symm c.2)
            apply j
          have pr : (reducePathAux ex h₁ h₂ (cons ey h₃ h₄ eyz)).1 = (ih ▸ eyz) := by
            simp[reducePathAux, c]
          let k := Quot.sound (Eq.symm pr ▸ this)
          exact (Eq.symm k)
    · have :
          reducePathAux ex h₁ h₂ (cons ey h₃ h₄ eyz) =
            cons ex h₁ h₂ (cons ey h₃ h₄ eyz) := by
        simp[reducePathAux, c]
      simp [this]

/-- proves that reducePath preserves the homotopy class -/
theorem homotopy_reducePath [DecidableEq V] [DecidableEq E] {G : Graph V E} {x y : V}
    (p₁ : EdgePath G x y) : homotopy p₁ (reducePath p₁) := by
        induction p₁ with
        | single x =>
          simp [homotopy, htclass, reducePath]
        | cons ex h₁ h₂ exy ih' =>
          let p₃ := reducePath exy
          let q := p₃.1
          let p₄ := reducePathAux ex h₁ h₂ q
          have : p₄.1 = (reducePath (cons ex h₁ h₂ exy)).1 := by
            simp [reducePath, p₃, q, p₄]
          have t₁ : homotopy (cons ex h₁ h₂ q) (p₄.1) := by
            apply homotopy_reducePathAux ex h₁ h₂ q
          have t₂ : homotopy exy q := by apply ih'
          have t₃ : homotopy (cons ex h₁ h₂ exy) (cons ex h₁ h₂ q) := by
            apply homotopy_left_mult_edge exy q t₂ ex h₁ h₂
          apply homotopy_trans (cons ex h₁ h₂ exy) (cons ex h₁ h₂ q)
            (reducePath (cons ex h₁ h₂ exy)) t₃ (this ▸ t₁)





instance htMul {G : Graph V E} {x : V} : Mul (ht G x x) where
  mul : ht G x x → ht G x x → ht G x x := fun a b => homotopyMultiplication a b

--defines the identity homotopy class
instance htOne {G : Graph V E} {x : V} : One (ht G x x) where
  one : ht G x x := htclass (single x)

/-- proves that multiplication of homotopy classes is associative -/
theorem ht_mult_assoc {G : Graph V E} {x : V} (a b c : ht G x x) :
    ((a # b) # c) = (a # (b # c)) := by
  let k := @homotopy_mult_assoc V E G x x x x
  let l (a b c : ht G x x) := k b c a
  apply (l a b c)

/-- proves that the identity homotopy class is the right multiplicative identity -/
theorem ht_right_identity {G : Graph V E} {x : V} :
    (a₀ : ht G x x) → htMul.mul a₀ (@htOne V E G x).one = a₀ := by
  have k (b : EdgePath G x x) :
      homotopyMultiplication (htclass b) (htclass (single x)) = htclass b := by
    let l := mult_const b ▸ homotopy_left_multiplication_class b (single x)
    have :
        (htclass b) # (htclass (single x)) =
          homotopyLeftMultiplication b (htclass (single x)) := by
      rfl
    apply Eq.trans this l
  have k₂ (b : EdgePath G x x) :
      htMul.mul (htclass b) (@htOne V E G x).one = htclass b := by
    apply k
  apply Quot.ind
  apply k₂

/-- proves that the identity homotopy class is the left multiplicative identity -/
theorem ht_left_identity {G : Graph V E} {x : V} :
    (a₀ : ht G x x) → htMul.mul (@htOne V E G x).one a₀ = a₀ := by
  have k (b : EdgePath G x x) :
      homotopyMultiplication (htclass (single x)) (htclass b) = htclass b := by
    exact homotopy_left_multiplication_class (single x) b
  have k₂ (b : EdgePath G x x) :
      htMul.mul (@htOne V E G x).one (htclass b) = htclass b := by
    apply k
  apply Quot.ind
  apply k₂

instance htSemigroup {G : Graph V E} {x : V} : Semigroup (ht G x x) where
  mul := (@htMul V E G x).mul
  mul_assoc := by apply ht_mult_assoc

/-- The monoid structure on loops at a vertex modulo homotopy. -/
@[reducible] def htMonoid (G : Graph V E) (x : V) : Monoid (ht G x x) where
  mul := (· # ·)
  mul_assoc := ht_mult_assoc
  one := htclass (single x)
  one_mul := ht_left_identity
  mul_one := ht_right_identity

end LeanPool.Polylean
