module
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshEuler

/-! Actual frontier-vertex counts under genuine geometric ear deletion. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Classical
namespace LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh
noncomputable section
variable (M : TriangleMesh)

/-- Used vertices on the genuine frontier of the actual planar support. -/
def boundaryVertices : Finset M.Vertex :=
  M.usedVertices.filter (fun v => M.position v ∈ frontier M.toPlaneComplex.support)

def boundaryVerticesOutside (T : M.Triangle) : Finset M.Vertex :=
  M.usedVertices.filter (fun v => M.position v ∈ frontier M.toPlaneComplex.support ∧
    M.position v ∉ M.triangleCarrier T.1)

theorem boundaryVertices_erase (T : M.Triangle) :
    (M.eraseTriangle T.1).boundaryVertices = M.usedVertices.filter
      (fun v => M.position v ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
  ext v
  simp only [boundaryVertices, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hp⟩
    refine ⟨?_, hp⟩
    rw [← M.usedVertices_erase_union T]
    exact Finset.mem_union_left _ hv
  · rintro ⟨hv, hp⟩
    refine ⟨(M.position_mem_erase_support_iff hv T).mp ?_, hp⟩
    exact (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp

theorem position_mem_freeBase_iff (T : M.Triangle) (k : Fin 3)
    {v : M.Vertex} (hv : v ∈ M.usedVertices) :
    M.position v ∈ segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) ↔
      v ∈ M.freeTriangleBaseEdge T k := by
  rw [← M.freeTriangleBaseEdge_carrier T k]
  constructor
  · intro hp
    have hpT : M.position v ∈ M.triangleCarrier T.1 :=
      convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k)) hp
    exact M.vertex_mem_edge_of_position_mem_edgeCarrier T.2
      (M.mem_triangle_of_position_mem hv T.2 hpT) (M.freeTriangleBaseEdge_mem_edges T k) hp
  · exact fun hv => subset_convexHull ℝ _ ⟨v,hv,rfl⟩

theorem position_mem_freeApex_iff (T : M.Triangle) (k : Fin 3)
    {v : M.Vertex} (hv : v ∈ M.usedVertices) :
    M.position v ∈ (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
      segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) ↔ v ∈ T.1 := by
  constructor
  · intro hp
    apply M.mem_triangle_of_position_mem hv T.2
    rcases hp with hp | hp
    · rw [← M.freeTriangleApexEdge0_carrier T k] at hp
      exact convexHull_mono (Set.image_mono (M.freeTriangleApexEdge0_subset T k)) hp
    · rw [← M.freeTriangleApexEdge1_carrier T k] at hp
      exact convexHull_mono (Set.image_mono (M.freeTriangleApexEdge1_subset T k)) hp
  · exact M.triangleVertex_mem_freeTriangleApexEdges T k

theorem filter_frontier_trace_union (T : M.Triangle) (U : Set Plane)
    (s : Finset M.Vertex) (hs : s ⊆ M.usedVertices)
    (htrace : ∀ v ∈ M.usedVertices, M.position v ∈ U ↔ v ∈ s) :
    M.usedVertices.filter (fun v => M.position v ∈
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪ U) =
      M.boundaryVerticesOutside T ∪ s := by
  ext v
  simp only [Finset.mem_filter, Set.mem_union, Set.mem_sdiff, Finset.mem_union,
    boundaryVerticesOutside]
  constructor
  · rintro ⟨hv, h | h⟩
    · exact Or.inl ⟨hv,h⟩
    · exact Or.inr ((htrace v hv).mp h)
  · rintro (⟨hv,h⟩ | hv)
    · exact ⟨hv,Or.inl h⟩
    · exact ⟨hs hv,Or.inr ((htrace v (hs hv)).mpr hv)⟩

theorem boundaryVerticesOutside_disjoint_triangle (T : M.Triangle) :
    Disjoint (M.boundaryVerticesOutside T) T.1 := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvO hvT
  exact (Finset.mem_filter.mp hvO).2.2 (subset_convexHull ℝ _ ⟨v,hvT,rfl⟩)

theorem boundaryVertices_erase_card_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    (M.eraseTriangle T.1).boundaryVertices.card = M.boundaryVertices.card + 1 := by
  have hT : T.1 ⊆ M.usedVertices := fun v hv => M.mem_usedVertices.mpr ⟨T.1,T.2,hv⟩
  have hB := M.filter_frontier_trace_union T _ (M.freeTriangleBaseEdge T k)
    ((M.freeTriangleBaseEdge_subset T k).trans hT)
    (fun v hv => M.position_mem_freeBase_iff T k hv)
  have hA := M.filter_frontier_trace_union T _ T.1 hT
    (fun v hv => M.position_mem_freeApex_iff T k hv)
  have hOld : M.boundaryVertices = M.boundaryVerticesOutside T ∪ M.freeTriangleBaseEdge T k := by
    ext v
    simp only [boundaryVertices, Finset.mem_filter]
    rw [M.frontier_eq_outside_triangle_union_base_of_oneEdgeFree T k hfree]
    simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hB v)
  have hNew : (M.eraseTriangle T.1).boundaryVertices = M.boundaryVerticesOutside T ∪ T.1 := by
    rw [M.boundaryVertices_erase T]
    ext v
    simp only [Finset.mem_filter]
    rw [M.frontier_eraseTriangle_support_of_oneEdgeFree T k hfree]
    simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hA v)
  have hd := M.boundaryVerticesOutside_disjoint_triangle T
  have hdB := hd.mono_right (M.freeTriangleBaseEdge_subset T k)
  rw [hOld, hNew, Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hdB,
    M.card_triangle T.1 T.2, M.freeTriangleBaseEdge_card T k]

theorem boundaryVertices_erase_card_of_twoEdgeFree (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    M.boundaryVertices.card = (M.eraseTriangle T.1).boundaryVertices.card + 1 := by
  have hT : T.1 ⊆ M.usedVertices := fun v hv => M.mem_usedVertices.mpr ⟨T.1,T.2,hv⟩
  have hB := M.filter_frontier_trace_union T _ (M.freeTriangleBaseEdge T k)
    ((M.freeTriangleBaseEdge_subset T k).trans hT)
    (fun v hv => M.position_mem_freeBase_iff T k hv)
  have hA := M.filter_frontier_trace_union T _ T.1 hT
    (fun v hv => M.position_mem_freeApex_iff T k hv)
  have hOld : M.boundaryVertices = M.boundaryVerticesOutside T ∪ T.1 := by
    ext v
    simp only [boundaryVertices, Finset.mem_filter]
    rw [M.frontier_eq_outside_triangle_union_apex_of_twoEdgeFree T k hfree]
    simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hA v)
  obtain ⟨J',hR,hI⟩ := M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k hfree
  have hNew : (M.eraseTriangle T.1).boundaryVertices =
      M.boundaryVerticesOutside T ∪ M.freeTriangleBaseEdge T k := by
    have hf := M.frontier_eraseTriangle_support T
    rw [hR, hI] at hf
    rw [M.boundaryVertices_erase T]
    ext v
    simp only [Finset.mem_filter]
    rw [hR, hf]
    simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hB v)
  have hd := M.boundaryVerticesOutside_disjoint_triangle T
  have hdB := hd.mono_right (M.freeTriangleBaseEdge_subset T k)
  rw [hOld, hNew, Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hdB,
    M.card_triangle T.1 T.2, M.freeTriangleBaseEdge_card T k]

/-- The disk count in precisely the form needed for actual corner sums. -/
def boundaryDiskCharacteristic : ℤ :=
  2 * (M.usedVertices.card : ℤ) - M.triangles.card - M.boundaryVertices.card

theorem boundaryDiskCharacteristic_erase_of_oneEdgeFree (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    M.boundaryDiskCharacteristic = (M.eraseTriangle T.1).boundaryDiskCharacteristic := by
  have hV := Finset.card_union_add_card_inter (M.eraseTriangle T.1).usedVertices T.1
  rw [M.usedVertices_erase_union T, M.usedVertices_inter_triangle_of_oneEdgeFree T k hfree] at hV
  have hF := M.card_eraseTriangle_triangles T.2
  have hB := M.boundaryVertices_erase_card_of_oneEdgeFree T k hfree
  unfold boundaryDiskCharacteristic
  omega

theorem boundaryDiskCharacteristic_erase_of_twoEdgeFree (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    M.boundaryDiskCharacteristic = (M.eraseTriangle T.1).boundaryDiskCharacteristic := by
  have hV := Finset.card_union_add_card_inter (M.eraseTriangle T.1).usedVertices T.1
  rw [M.usedVertices_erase_union T,
    M.usedVertices_inter_triangle_of_twoEdgeFree J hsupport T k hfree,
    M.card_triangle T.1 T.2, M.freeTriangleBaseEdge_card T k] at hV
  have hF := M.card_eraseTriangle_triangles T.2
  have hB := M.boundaryVertices_erase_card_of_twoEdgeFree J hsupport T k hfree
  unfold boundaryDiskCharacteristic
  omega

theorem boundaryVertices_of_card_one (hcard : M.triangles.card = 1) :
    M.boundaryVertices = M.usedVertices := by
  obtain ⟨t,htri⟩ := Finset.card_eq_one.mp hcard
  have ht : t ∈ M.triangles := by rw [htri]; simp
  have hb (e : Finset M.Vertex) (he : e ∈ M.edges) : M.IsBoundaryEdge e := by
    refine ⟨he, ?_⟩
    obtain ⟨u,hu,heu⟩ := Finset.mem_biUnion.mp he
    have hut : u = t := by simpa only [htri, Finset.mem_singleton] using hu
    have het : e ⊆ t := hut ▸ (Finset.mem_powersetCard.mp heu).1
    have hi : M.incidentTriangles e = {t} := by
      ext u
      simp only [M.mem_incidentTriangles_iff, htri, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl,het⟩
    rw [hi]
    simp
  apply Finset.Subset.antisymm (Finset.filter_subset _ _)
  intro v hv
  have hvt : v ∈ t := by simpa [usedVertices, htri] using hv
  let T : M.Triangle := ⟨t,ht⟩
  have hp := M.triangleVertex_mem_freeTriangleApexEdges T 0 hvt
  have hf : M.position v ∈ frontier M.toPlaneComplex.support := by
    rcases hp with hp | hp
    · apply M.boundaryEdgeCarrier_subset_frontier (hb _ (M.freeTriangleApexEdge0_mem_edges T 0))
      rwa [M.freeTriangleApexEdge0_carrier T 0]
    · apply M.boundaryEdgeCarrier_subset_frontier (hb _ (M.freeTriangleApexEdge1_mem_edges T 0))
      rwa [M.freeTriangleApexEdge1_carrier T 0]
  exact Finset.mem_filter.mpr ⟨hv,hf⟩

theorem boundaryDiskCharacteristic_of_card_one (hcard : M.triangles.card = 1) :
    M.boundaryDiskCharacteristic = 2 := by
  obtain ⟨t,htri⟩ := Finset.card_eq_one.mp hcard
  have ht : t ∈ M.triangles := by rw [htri]; simp
  have hV : M.usedVertices.card = 3 := by
    simpa [usedVertices,htri] using M.card_triangle t ht
  unfold boundaryDiskCharacteristic
  rw [M.boundaryVertices_of_card_one hcard, hV, hcard]
  norm_num

/-- The boundary-vertex disk count follows from actual geometric deletion, without a supplied cycle. -/
theorem boundaryDiskCharacteristic_of_polygonalDisk (J : PolygonalCircle)
    (hsupport : M.toPlaneComplex.support = J.closedRegion) :
    M.boundaryDiskCharacteristic = 2 := by
  induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M J with
  | h n ih =>
    have hpos : 0 < M.triangles.card := by
      apply Finset.card_pos.mpr
      by_contra hempty
      have hempty' := Finset.not_nonempty_iff_eq_empty.mp hempty
      obtain ⟨p,hp⟩ := J.isConnected_interiorRegion.nonempty
      have hpclosed : p ∈ J.closedRegion := by
        rw [J.closedRegion_eq_union]
        exact Or.inl hp
      rw [← hsupport, toPlaneComplex_support, hempty'] at hpclosed
      simp at hpclosed
    by_cases hone : M.triangles.card = 1
    · exact M.boundaryDiskCharacteristic_of_card_one hone
    have hmore : 1 < M.triangles.card := by omega
    obtain ⟨T,U,hTU,⟨k,hfree⟩,hU⟩ :=
      M.exists_two_geometricallyFreeTriangles_of_polygonalDisk J hsupport hmore
    have hsmall : (M.eraseTriangle T.1).triangles.card < n := by
      have hF := M.card_eraseTriangle_triangles T.2
      omega
    rcases hfree with hone | htwo
    · obtain ⟨J',hR⟩ :=
        M.exists_polygonalDisk_eraseTriangle_of_oneEdgeFree J hsupport T k hone hmore
      calc
        M.boundaryDiskCharacteristic = (M.eraseTriangle T.1).boundaryDiskCharacteristic :=
          M.boundaryDiskCharacteristic_erase_of_oneEdgeFree T k hone
        _ = 2 := ih _ hsmall (M.eraseTriangle T.1) J' hR rfl
    · obtain ⟨J',hR,hI⟩ :=
        M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hsupport T k htwo
      calc
        M.boundaryDiskCharacteristic = (M.eraseTriangle T.1).boundaryDiskCharacteristic :=
          M.boundaryDiskCharacteristic_erase_of_twoEdgeFree J hsupport T k htwo
        _ = 2 := ih _ hsmall (M.eraseTriangle T.1) J' hR rfl

end
end LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh
