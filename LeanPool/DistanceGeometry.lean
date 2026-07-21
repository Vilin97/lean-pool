/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.DistanceGeometry.Defs
import LeanPool.DistanceGeometry.Schoenberg
import LeanPool.DistanceGeometry.SchoenbergHard
import LeanPool.DistanceGeometry.Trilateration
import LeanPool.DistanceGeometry.CayleyMengerVolume

/-!
# Euclidean Distance Geometry

Source: doi:10.2307/1968654
Authors: Egor Lyfar
Status: verified
Main declarations: `DistanceGeometry.schoenberg`, `DistanceGeometry.encard_setOf_forall_dist_eq_le_two`, `DistanceGeometry.trilateration_le_two`, `DistanceGeometry.cayleyMenger_det_heron`
Tags: distance-geometry, euclidean-geometry, linear-algebra, positive-semidefinite-matrices, cayley-menger
MSC: 51K05, 52C99, 15A18
-/

/-!
This project develops three parts of finite Euclidean distance geometry: both
directions of Schoenberg's centered-Gram characterization with a rank-controlled
positive-semidefinite factorization, a codimension-one trilateration bound, and
the Cayley--Menger determinant through the segment and triangle cases, including
Heron's formula.
-/
