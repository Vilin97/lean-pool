/-
Copyright (c) 2026 André Hernandez-Espiet, Vladimir Sedlacek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet, Vladimir Sedlacek
-/
import LeanPool.SyntheticEuclid4.SyntheticEuclid4

/-!
# Synthetic Euclidean geometry: Euclid's Elements Book I

Source: doi:10.1017/S1755020309990098, url:https://github.com/ah1112/synthetic_euclid_4
Authors: André Hernandez-Espiet, Vladimir Sedlacek
Status: verified
Main declarations: `SyntheticEuclid4.pythagoras`, `SyntheticEuclid4.pythagoras_converse`
Tags: euclidean-geometry, synthetic-geometry, pythagorean-theorem
MSC: 51M04
-/

/-!
A formalization of Book I of Euclid's *Elements* in Lean 4, built on Avigad,
Dean, and Mumma's axiomatic system for synthetic geometry (incidence,
betweenness, congruence, and area primitives). It develops the API for points,
lines, circles, triangles, parallelograms, and squares, includes custom
permutation tactics (`perm`, `perma`, `linperm`) for the symmetric area and
angle relations, and culminates in the Pythagorean theorem (Euclid I.47) and its
converse (Euclid I.48).
-/
