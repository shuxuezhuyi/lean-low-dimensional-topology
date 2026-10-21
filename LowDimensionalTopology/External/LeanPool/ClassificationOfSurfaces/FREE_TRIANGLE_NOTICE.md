# Triangle mesh proof attribution

FreeTriangle.lean is adapted from LeanPool/lean-pool at commit 86da5902e640ceb44e53f88c4a04f870dc062126.

Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Authors: Ryan McCorvie, Jack McCarthy.
Released under the Apache License, Version 2.0; the full license is retained at LowDimensionalTopology/External/LeanPool/LICENSE. Original copyright and authorship headers remain in the Lean file.

This complete single-file extension supplies actual affine triangle-face intersection and boundary-edge geometry over the existing separately documented mesh port. Imports are redirected to project paths and made public. Original declaration names, theorem statements and proof bodies remain unchanged. FREE_TRIANGLE_UPSTREAM.json records the exact upstream Git blob, original and adapted SHA-256 hashes and all 75 public declaration mappings.

The weak IsFreeTriangle predicate is explicitly an incidence-one-edge precursor; it does not assert geometric shellability or a polygonal disk deletion conclusion. This module alone does not prove Euler characteristic or the book polygon area formula. Native hyperbolic transport and density-area proofs are original and remain separate. No new toolchain, Mathlib pin or external Lake dependency is introduced.
