module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.PolygonalDiskDeletion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Pointwise

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh

variable (M : TriangleMesh)

/-- Only vertices used by an actual face count in the finite mesh. -/
def usedVertices : Finset M.Vertex := M.triangles.biUnion id

theorem mem_usedVertices {v : M.Vertex} :
    v ∈ M.usedVertices ↔ ∃ t ∈ M.triangles, v ∈ t := by
  classical
  simp [usedVertices]

theorem mem_triangle_of_position_mem {v : M.Vertex} (hv : v ∈ M.usedVertices)
    {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (hp : M.position v ∈ M.triangleCarrier t) : v ∈ t := by
  classical
  obtain ⟨u, hu, hvu⟩ := M.mem_usedVertices.mp hv
  have hs : ({v} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨by simp, u, hu, by simpa using hvu⟩
  have ht' : t ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; decide),
      t, ht, Subset.rfl⟩
  have hface := M.toPlaneComplex.face_inter {v} hs t ht'
  change convexHull ℝ (M.position '' (({v} : Finset M.Vertex) : Set M.Vertex)) ∩
      M.triangleCarrier t =
    convexHull ℝ (M.position '' (({v} ∩ t : Finset M.Vertex) : Set M.Vertex)) at hface
  have hmem : M.position v ∈
      convexHull ℝ (M.position '' (({v} ∩ t : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface]
    exact ⟨by simp, hp⟩
  by_contra hvnot
  have hempty : ({v} ∩ t : Finset M.Vertex) = ∅ := by simp [hvnot]
  simp [hempty] at hmem

theorem position_mem_erase_support_iff {v : M.Vertex} (hv : v ∈ M.usedVertices)
    (T : M.Triangle) :
    M.position v ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
      v ∈ (M.eraseTriangle T.1).usedVertices := by
  classical
  rw [toPlaneComplex_support]
  simp only [Set.mem_iUnion, mem_usedVertices, eraseTriangle_triangles]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, M.mem_triangle_of_position_mem hv (Finset.mem_erase.mp ht).2 hp⟩
  · rintro ⟨t, ht, hvt⟩
    refine ⟨t, ht, ?_⟩
    exact subset_convexHull ℝ _ ⟨v, hvt, rfl⟩

theorem usedVertices_erase_union (T : M.Triangle) :
    (M.eraseTriangle T.1).usedVertices ∪ T.1 = M.usedVertices := by
  classical
  ext v
  simp only [Finset.mem_union, mem_usedVertices, eraseTriangle_triangles,
    Finset.mem_erase]
  constructor
  · rintro (⟨t, ⟨hne, ht⟩, hvt⟩ | hvT)
    · exact ⟨t, ht, hvt⟩
    · exact ⟨T.1, T.2, hvT⟩
  · rintro ⟨t, ht, hvt⟩
    by_cases heq : t = T.1
    · exact Or.inr (heq ▸ hvt)
    · exact Or.inl ⟨t, ⟨heq, ht⟩, hvt⟩

theorem edges_erase_union (T : M.Triangle) :
    (M.eraseTriangle T.1).edges ∪ M.triangleEdges T.1 = M.edges := by
  classical
  ext e
  simp only [Finset.mem_union, edges, triangleEdges, Finset.mem_biUnion,
    eraseTriangle_triangles, Finset.mem_erase]
  constructor
  · rintro (⟨t, ⟨hne, ht⟩, het⟩ | heT)
    · exact ⟨t, ht, het⟩
    · exact ⟨T.1, T.2, heT⟩
  · rintro ⟨t, ht, het⟩
    by_cases heq : t = T.1
    · exact Or.inr (heq ▸ het)
    · exact Or.inl ⟨t, ⟨heq, ht⟩, het⟩

/-- The finite Euler count uses exactly the simplices that occur in the actual mesh. -/
def eulerCharacteristic : ℤ :=
  (M.usedVertices.card : ℤ) - M.edges.card + M.triangles.card

theorem eulerCharacteristic_erase (T : M.Triangle) :
    M.eulerCharacteristic = (M.eraseTriangle T.1).eulerCharacteristic + 1 -
      (((M.eraseTriangle T.1).usedVertices ∩ T.1).card : ℤ) +
      (((M.eraseTriangle T.1).edges ∩ M.triangleEdges T.1).card : ℤ) := by
  classical
  have hV := Finset.card_union_add_card_inter
    (M.eraseTriangle T.1).usedVertices T.1
  rw [M.usedVertices_erase_union T, M.card_triangle T.1 T.2] at hV
  have hE := Finset.card_union_add_card_inter
    (M.eraseTriangle T.1).edges (M.triangleEdges T.1)
  have he3 : (M.triangleEdges T.1).card = 3 := by
    simp [triangleEdges, M.card_triangle T.1 T.2]
  rw [M.edges_erase_union T, he3] at hE
  have hF := M.card_eraseTriangle_triangles T.2
  unfold eulerCharacteristic
  omega

theorem mem_erase_edges_iff_not_boundary (T : M.Triangle) {e : Finset M.Vertex}
    (hecard : e.card = 2) (heT : e ⊆ T.1) :
    e ∈ (M.eraseTriangle T.1).edges ↔ ¬M.IsBoundaryEdge e := by
  classical
  constructor
  · intro he hboundary
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
    have hu' := Finset.mem_erase.mp hu
    have hTinc : T.1 ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
    have hUinc : u ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨hu'.2, (Finset.mem_powersetCard.mp heu).1⟩
    have htwo := Finset.one_lt_card.mpr ⟨u, hUinc, T.1, hTinc, hu'.1⟩
    have hb := hboundary.2
    omega
  · intro hnot
    have htwo := M.card_incidentTriangles_eq_two_of_not_boundary T.2 hecard heT hnot
    have hTinc : T.1 ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
    have hother : ∃ u ∈ M.incidentTriangles e, u ≠ T.1 := by
      by_contra h
      push Not at h
      have hsingle : M.incidentTriangles e = {T.1} := by
        ext u
        exact ⟨fun hu => Finset.mem_singleton.mpr (h u hu),
          fun hu => (Finset.mem_singleton.mp hu) ▸ hTinc⟩
      simp [hsingle] at htwo
    obtain ⟨u, hu, hne⟩ := hother
    have hud := M.mem_incidentTriangles_iff.mp hu
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨hne, hud.1⟩,
      Finset.mem_powersetCard.mpr ⟨hud.2, hecard⟩⟩

theorem usedVertices_inter_triangle_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).usedVertices ∩ T.1 = T.1 := by
  classical
  apply Finset.Subset.antisymm Finset.inter_subset_right
  intro v hvT
  refine Finset.mem_inter.mpr ⟨?_, hvT⟩
  have hv : v ∈ M.usedVertices := M.mem_usedVertices.mpr ⟨T.1, T.2, hvT⟩
  apply (M.position_mem_erase_support_iff hv T).mp
  have hp := M.triangleVertex_mem_freeTriangleApexEdges T k hvT
  rw [← M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree] at hp
  exact hp.1

theorem boundaryEdge_eq_base_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) {e : Finset M.Vertex}
    (heT : e ⊆ T.1) (he : M.IsBoundaryEdge e) : e = M.freeTriangleBaseEdge T k := by
  classical
  have hsub : e ⊆ M.freeTriangleBaseEdge T k := by
    intro v hv
    have hpEdge : M.position v ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) :=
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    have hpF := M.boundaryEdgeCarrier_subset_frontier he hpEdge
    have hpT : M.position v ∈ M.triangleCarrier T.1 :=
      subset_convexHull ℝ _ ⟨v, heT hv, rfl⟩
    have hpBase : M.position v ∈ segment ℝ (M.freeTriangleOrder T k 0)
        (M.freeTriangleOrder T k 1) := hfree ▸ ⟨hpF, hpT⟩
    apply M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 (heT hv)
      (M.freeTriangleBaseEdge_mem_edges T k)
    rwa [M.freeTriangleBaseEdge_carrier T k]
  exact Finset.eq_of_subset_of_card_le hsub (by
    rw [M.freeTriangleBaseEdge_card T k, M.card_of_mem_edges he.1])

theorem edges_inter_triangle_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).edges ∩ M.triangleEdges T.1 =
      (M.triangleEdges T.1).erase (M.freeTriangleBaseEdge T k) := by
  classical
  ext e
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨heR, heT⟩
    have hed := Finset.mem_powersetCard.mp heT
    refine ⟨?_, heT⟩
    intro heq
    have hnot := (M.mem_erase_edges_iff_not_boundary T hed.2 hed.1).mp heR
    exact hnot (heq ▸ M.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree T k hfree)
  · rintro ⟨hne, heT⟩
    have hed := Finset.mem_powersetCard.mp heT
    refine ⟨(M.mem_erase_edges_iff_not_boundary T hed.2 hed.1).mpr ?_, heT⟩
    intro he
    exact hne (M.boundaryEdge_eq_base_of_oneEdgeFree T k hfree hed.1 he)

theorem eulerCharacteristic_erase_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    M.eulerCharacteristic = (M.eraseTriangle T.1).eulerCharacteristic := by
  classical
  have hV := congrArg Finset.card (M.usedVertices_inter_triangle_of_oneEdgeFree T k hfree)
  have hE := congrArg Finset.card (M.edges_inter_triangle_of_oneEdgeFree T k hfree)
  have heMem : M.freeTriangleBaseEdge T k ∈ M.triangleEdges T.1 :=
    Finset.mem_powersetCard.mpr
      ⟨M.freeTriangleBaseEdge_subset T k, M.freeTriangleBaseEdge_card T k⟩
  have h3 : (M.triangleEdges T.1).card = 3 := by
    simp [triangleEdges, M.card_triangle T.1 T.2]
  have herase := Finset.card_erase_of_mem heMem
  have hT := M.card_triangle T.1 T.2
  have hχ := M.eulerCharacteristic_erase T
  omega

theorem usedVertices_inter_triangle_of_twoEdgeFree (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).usedVertices ∩ T.1 = M.freeTriangleBaseEdge T k := by
  classical
  obtain ⟨J', hR, hI⟩ :=
    M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k hfree
  have htrace : (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
    rwa [hR]
  ext v
  constructor
  · intro hv
    have hvd := Finset.mem_inter.mp hv
    have hvOld : v ∈ M.usedVertices := M.mem_usedVertices.mpr ⟨T.1, T.2, hvd.2⟩
    have hpR := (M.position_mem_erase_support_iff hvOld T).mpr hvd.1
    have hpT : M.position v ∈ M.triangleCarrier T.1 :=
      subset_convexHull ℝ _ ⟨v, hvd.2, rfl⟩
    have hpBase : M.position v ∈ segment ℝ (M.freeTriangleOrder T k 0)
        (M.freeTriangleOrder T k 1) := htrace ▸ ⟨hpR, hpT⟩
    apply M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 hvd.2
      (M.freeTriangleBaseEdge_mem_edges T k)
    rwa [M.freeTriangleBaseEdge_carrier T k]
  · intro hv
    have hvT := M.freeTriangleBaseEdge_subset T k hv
    refine Finset.mem_inter.mpr ⟨?_, hvT⟩
    have hvOld : v ∈ M.usedVertices := M.mem_usedVertices.mpr ⟨T.1, T.2, hvT⟩
    apply (M.position_mem_erase_support_iff hvOld T).mp
    have hpBase : M.position v ∈ convexHull ℝ
        (M.position '' (M.freeTriangleBaseEdge T k : Set M.Vertex)) :=
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    rw [M.freeTriangleBaseEdge_carrier T k, ← htrace] at hpBase
    exact hpBase.1

theorem edge_mem_erase_of_carrier_subset (T : M.Triangle) {e : Finset M.Vertex}
    (hecard : e.card = 2) (heT : e ⊆ T.1)
    (hsub : convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.eraseTriangle T.1).toPlaneComplex.support) :
    e ∈ (M.eraseTriangle T.1).edges := by
  classical
  obtain ⟨p, hp, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hecard
  have hpR := hsub hp
  rw [toPlaneComplex_support] at hpR
  simp only [Set.mem_iUnion, eraseTriangle_triangles] at hpR
  obtain ⟨u, hu, hpU⟩ := hpR
  have hu' := Finset.mem_erase.mp hu
  have heu := M.edge_subset_of_nonvertex_mem_triangleCarrier hecard heT T.2 hu'.2
    hp hpU hpv
  exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_powersetCard.mpr ⟨heu, hecard⟩⟩

theorem edges_inter_triangle_of_twoEdgeFree (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).edges ∩ M.triangleEdges T.1 =
      {M.freeTriangleBaseEdge T k} := by
  classical
  have hV := M.usedVertices_inter_triangle_of_twoEdgeFree J hsupport T k hfree
  obtain ⟨J', hR, hI⟩ :=
    M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k hfree
  ext e
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨heR, heT⟩
    have heT' := Finset.mem_powersetCard.mp heT
    have hsub : e ⊆ M.freeTriangleBaseEdge T k := by
      intro v hv
      rw [← hV]
      refine Finset.mem_inter.mpr ⟨?_, heT'.1 hv⟩
      obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp heR
      exact (M.eraseTriangle T.1).mem_usedVertices.mpr
        ⟨u, hu, (Finset.mem_powersetCard.mp heu).1 hv⟩
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [M.freeTriangleBaseEdge_card T k, heT'.2])
  · rintro rfl
    refine ⟨?_, Finset.mem_powersetCard.mpr
      ⟨M.freeTriangleBaseEdge_subset T k, M.freeTriangleBaseEdge_card T k⟩⟩
    apply M.edge_mem_erase_of_carrier_subset T (M.freeTriangleBaseEdge_card T k)
      (M.freeTriangleBaseEdge_subset T k)
    rw [M.freeTriangleBaseEdge_carrier T k, hR]
    intro p hp
    exact (hI.symm ▸ hp).1

theorem eulerCharacteristic_erase_of_twoEdgeFree (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    M.eulerCharacteristic = (M.eraseTriangle T.1).eulerCharacteristic := by
  classical
  have hV := congrArg Finset.card
    (M.usedVertices_inter_triangle_of_twoEdgeFree J hsupport T k hfree)
  have hE := congrArg Finset.card
    (M.edges_inter_triangle_of_twoEdgeFree J hsupport T k hfree)
  have h2 := M.freeTriangleBaseEdge_card T k
  have hχ := M.eulerCharacteristic_erase T
  simp only [Finset.card_singleton] at hE
  omega

theorem eulerCharacteristic_of_card_one (hcard : M.triangles.card = 1) :
    M.eulerCharacteristic = 1 := by
  classical
  obtain ⟨t, htri⟩ := Finset.card_eq_one.mp hcard
  have ht : t ∈ M.triangles := by rw [htri]; simp
  have h3 := M.card_triangle t ht
  simp [eulerCharacteristic, usedVertices, edges, htri, h3]

/-- Euler's disk count follows by actual geometric ear deletion; no shelling is supplied. -/
theorem eulerCharacteristic_of_polygonalDisk (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion) :
    M.eulerCharacteristic = 1 := by
  classical
  induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M J with
  | h n ih =>
    have hpos : 0 < M.triangles.card := by
      apply Finset.card_pos.mpr
      by_contra hempty
      have hempty' := Finset.not_nonempty_iff_eq_empty.mp hempty
      obtain ⟨p, hp⟩ := J.isConnected_interiorRegion.nonempty
      have hpclosed : p ∈ J.closedRegion := by
        rw [J.closedRegion_eq_union]
        exact Or.inl hp
      rw [← hsupport, toPlaneComplex_support, hempty'] at hpclosed
      simp at hpclosed
    by_cases hone : M.triangles.card = 1
    · exact M.eulerCharacteristic_of_card_one hone
    have hmore : 1 < M.triangles.card := by omega
    obtain ⟨T, U, hTU, ⟨k, hfree⟩, hU⟩ :=
      M.exists_two_geometricallyFreeTriangles_of_polygonalDisk J hsupport hmore
    have hsmall : (M.eraseTriangle T.1).triangles.card < n := by
      have hF := M.card_eraseTriangle_triangles T.2
      omega
    rcases hfree with hone | htwo
    · obtain ⟨J', hR⟩ :=
        M.exists_polygonalDisk_eraseTriangle_of_oneEdgeFree J hsupport T k hone hmore
      calc
        M.eulerCharacteristic = (M.eraseTriangle T.1).eulerCharacteristic :=
          M.eulerCharacteristic_erase_of_oneEdgeFree T k hone
        _ = 1 := ih _ hsmall (M.eraseTriangle T.1) J' hR rfl
    · obtain ⟨J', hR, hI⟩ :=
        M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k htwo
      calc
        M.eulerCharacteristic = (M.eraseTriangle T.1).eulerCharacteristic :=
          M.eulerCharacteristic_erase_of_twoEdgeFree J hsupport T k htwo
        _ = 1 := ih _ hsmall (M.eraseTriangle T.1) J' hR rfl

end LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh
