# Geometric polygonal disk deletion proof attribution

These six modules are adapted from LeanPool/lean-pool at commit 86da5902e640ceb44e53f88c4a04f870dc062126.

Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Authors: Ryan McCorvie, Jack McCarthy.
Released under the Apache License, Version 2.0. The full license is retained at LowDimensionalTopology/External/LeanPool/LICENSE; original copyright and authorship headers remain in each Lean file.

AmbientHomeomorph, ElementaryMove, ThinKiteMove, FreeTriangleMove and PolygonalCrosscut are complete upstream files. Imports are redirected to project paths and made public. A few ring/abel closing tactics are normalized to ring_nf/abel_nf to avoid informational diagnostics. The theorem statements and mathematical arguments are unchanged.

PolygonalDiskDeletion extracts only the actual polygon edge-complex, geometric-ear and residual-disk results from PolygonalSchoenflies. Its new `TriangleMesh.exists_polygonalDisk_eraseTriangle_of_oneEdgeFree` is an original weakening of the upstream `PolygonalCircle.TriangleMesh.exists_supported_polygonalDisk_move_of_oneEdgeFree`: it instantiates the open neighborhood to the whole plane and retains only the actual remaining polygonal disk. Auxiliary ambient homeomorphism and finite-PL certificate outputs and their four unrelated dependencies are omitted. No new hypotheses or prescribed shelling are added.

DISK_DELETION_UPSTREAM.json records exact upstream Git blobs, original/adapted SHA-256 hashes, copied source ranges and all 386 explicit declaration mappings (351 public and 35 private). The original Euler proof and genuine hyperbolic angle/area transport are separate project work. This library foundation alone does not complete the book polygon area formula. Existing attribution manifests are unchanged.
