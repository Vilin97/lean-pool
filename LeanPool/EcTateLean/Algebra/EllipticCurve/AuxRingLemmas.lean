/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring


section ring_lemmas

variable {R : Type u} [CommRing R]

lemma factorize1 (root b p : R) (q : ℕ) :
    root * p ^ q * (p ^ q * b) + root * p ^ q * (root * p ^ q) =
      p ^ q * p ^ q * ((root + b) * root) := by ring

lemma factorize2 (root a p : R) (q : ℕ) :
    2 * (root * p ^ q) * (p ^ 1 * a) = p ^ q * p ^ 1 * (2 * a * root) := by ring

lemma factorize3 (root p : R) (q : ℕ) :
    3 * (root * p ^ q * (root * p ^ q)) = p ^ q * p ^ q * (3 * root * root) := by ring

lemma factorize4 (root a b c p : R) (q : ℕ) :
    p ^ (2 * q + 1) * c + root * p ^ q * (p ^ (q + 1) * b) + (root * p ^ q) ^ 2 * (p ^ 1 * a) =
      p ^ q * p ^ q * p ^ 1 * (a * root ^ 2) + p ^ q * p ^ (q + 1) * (b * root) +
        p ^ (2 * q + 1) * c := by ring

lemma factorize5 (b c p : R) :
    p ^ 1 * b * (p ^ 1 * b) + 4 * (p ^ 2 * c) = p ^ 2 * (b * b + 4 * c) := by ring

lemma factorize6 (p x b c : R) :
    p ^ 2 * x ^ 2 + p * x * (p ^ 1 * b) + p ^ 2 * -c = p ^ 2 * (1 * x ^ 2 + b * x + -c) := by ring

lemma factorize7 (a b r p : R) :
    p ^ 2 * a + 2 * (p * r) * (p ^ 1 * b) + 3 * (p * r) ^ 2 =
      p ^ 2 * (a + 2 * r * b + 3 * r ^ 2) := by ring

lemma factorize8 (a b c r p : R) :
    (p ^ 3 * a) + (p * r) * (p ^ 2 * b) + (p * r) ^ 2 * (p ^ 1 * c) + (p * r) ^ 3 =
      p ^ 3 * (a + r * b + r ^ 2 * c + r ^ 3) := by ring

lemma factorize9 (a1 a2 a3 a4 a6 b8 p : R) :
    p ^ 1 * a1 * (p ^ 1 * a1) * (p ^ 3 * a6) + p ^ 1 * a1 * (p ^ 2 * a3) * -a4 +
        4 * a2 * (p ^ 3 * a6) + a2 * (p ^ 2 * a3) * (p ^ 2 * a3) + p ^ 3 * -b8 =
      p ^ 3 * (p ^ 1 * a1 * (p ^ 1 * a1) * a6 + a1 * a3 * -a4 + 4 * a2 * a6 +
        a2 * a3 * (p ^ 1 * a3) + -b8) := by ring

end ring_lemmas
