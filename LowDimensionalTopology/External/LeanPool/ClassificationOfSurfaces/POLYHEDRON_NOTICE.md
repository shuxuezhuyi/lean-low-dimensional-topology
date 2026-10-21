# Polygonal polyhedron proof attribution

The two Lean files listed in POLYHEDRON_UPSTREAM.json are adapted from LeanPool/lean-pool at commit 86da5902e640ceb44e53f88c4a04f870dc062126.

Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Authors: Ryan McCorvie, Jack McCarthy.
Released under the Apache License, Version 2.0. The full license is retained at LowDimensionalTopology/External/LeanPool/LICENSE; original copyright and authorship headers remain in each Lean file.

This minimal extension adds LineSubdivision and PolygonalPolyhedron over the existing separately documented three-module polygonal Jordan port. It constructs actual finite triangle meshes of arbitrary polygonal closed regions. It does not assume a triangulation, convexity, a shelling, or a Jordan separation conclusion as an input.

Changes only redirect LeanPool imports to project module paths and make all imports public. Original global namespaces, declarations, theorem statements and proof bodies are unchanged. POLYHEDRON_UPSTREAM.json records exact upstream Git blob hashes, upstream and adapted SHA-256 hashes, and each public declaration mapping. No additional Lean toolchain, Mathlib pin or external Lake dependency is introduced.

Original project hyperbolic geometry, density-area and polygon transport proofs are maintained separately. This extension alone does not prove the book polygon area or angle-sum formula; those bridges remain in progress.
