/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedGeodesicRays
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Topology ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Closing a genuine convex region in the actual finite-and-ideal model retains genuine closed-model convexity. -/
theorem DiscHConvex.closedModel_closure {S : Set 𝔻} (hS : DiscHConvex S) :
    ClosedDiscHConvex (_root_.closure (discToClosedModel '' S)) := by
  apply (closedDiscHConvex_iff_klein_convex _).mpr
  rw [closedKlein_image_discClosedModelClosure]
  exact ((discHConvex_iff_klein_convex S).mp hS).closure

/-- The true interior of the true closure of a nonempty open h-convex region is the region itself. -/
theorem DiscHConvex.interior_closure_eq_of_isOpen {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) : _root_.interior (_root_.closure S)=S := by
  have hc:=((discHConvex_iff_klein_convex S).mp hS)
  have hfo : IsOpen (kleinCoordinate '' S):=isOpenEmbedding_kleinCoordinate.isOpenMap S ho
  have hfi : (_root_.interior (kleinCoordinate '' S)).Nonempty := by
    rw [hfo.interior_eq]
    exact hn.image kleinCoordinate
  have he : _root_.interior (_root_.closure (kleinCoordinate '' S))=kleinCoordinate '' S :=
    (hc.interior_closure_eq_interior_of_nonempty_interior hfi).trans hfo.interior_eq
  rw [isEmbedding_kleinCoordinate.closure_eq_preimage_closure_image S,
    ←isOpenEmbedding_kleinCoordinate.isOpenMap.preimage_interior_eq_interior_preimage
      continuous_kleinCoordinate,he,preimage_image_eq _ kleinCoordinate_injective]

/-- Three actual finite-or-ideal closure points force the whole true triangle interior into the original open convex region. -/
theorem ClosedDiscTriangle.interior_subset_of_vertices_mem_closedModelClosure
    (T : ClosedDiscTriangle) {S : Set 𝔻} (hS : DiscHConvex S) (ho : IsOpen S)
    (hn : S.Nonempty) (ha : T.a∈_root_.closure (discToClosedModel '' S))
    (hb : T.b∈_root_.closure (discToClosedModel '' S)) (hc : T.c∈_root_.closure (discToClosedModel '' S)) :
    T.interior⊆S := by
  have hclosed : T.closedCarrier⊆_root_.closure (discToClosedModel '' S) := by
    apply closedDiscHConvexHull_min hS.closedModel_closure
    intro p hp
    rcases hp with rfl|rfl|rfl
    · exact ha
    · exact hb
    · exact hc
  have hsub : T.interior⊆_root_.closure S := by
    intro z hz
    have hm : (z:ℂ)∈T.complexClosedCarrier:=interior_subset hz
    obtain ⟨p,hp,hpz⟩:=hm
    have he : p=discToClosedModel z := Subtype.ext hpz
    have hzcl : discToClosedModel z∈_root_.closure (discToClosedModel '' S):=he ▸ hclosed hp
    rw [isEmbedding_discToClosedModel.closure_eq_preimage_closure_image S]
    exact hzcl
  have hi : T.interior⊆_root_.interior (_root_.closure S):=interior_maximal hsub T.interior_isOpen
  rwa [hS.interior_closure_eq_of_isOpen ho hn] at hi

/-- Every actual all-ideal triangle has genuine density area pi. -/
theorem ClosedDiscTriangle.area_eq_pi_of_all_ideal (T : ClosedDiscTriangle)
    (ha : ‖(T.a:ℂ)‖=1) (hb : ‖(T.b:ℂ)‖=1) (hc : ‖(T.c:ℂ)‖=1) :
    discHyperbolicArea T.interior=ENNReal.ofReal Real.pi := by
  rw [T.area_eq_angle_defect,T.alpha_of_ideal ha,T.beta_of_ideal hb,T.gamma_of_ideal hc]
  simp only [sub_zero]

/-- Actual disjoint ideal fan triangles with vertices in the real compactified closure give their full pi-per-triangle area lower bound inside the original convex region. -/
theorem ideal_triangle_family_area_le {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (n : ℕ) (T : Fin n→ClosedDiscTriangle)
    (ha : ∀i,‖((T i).a:ℂ)‖=1) (hb : ∀i,‖((T i).b:ℂ)‖=1) (hc : ∀i,‖((T i).c:ℂ)‖=1)
    (haS : ∀i,(T i).a∈_root_.closure (discToClosedModel '' S))
    (hbS : ∀i,(T i).b∈_root_.closure (discToClosedModel '' S))
    (hcS : ∀i,(T i).c∈_root_.closure (discToClosedModel '' S))
    (hd : Pairwise (fun i j=>Disjoint (T i).interior (T j).interior)) :
    ENNReal.ofReal ((n:ℝ)*Real.pi)≤discHyperbolicArea S := by
  have hsub : (⋃i,(T i).interior)⊆S := by
    apply iUnion_subset
    intro i
    exact (T i).interior_subset_of_vertices_mem_closedModelClosure hS ho hn (haS i) (hbS i) (hcS i)
  have hm : discHyperbolicArea (⋃i,(T i).interior)=
      (n:ℝ≥0∞)*ENNReal.ofReal Real.pi := by
    have hcoe : Topology.IsOpenEmbedding ((↑):𝔻→ℂ):=
      (Metric.isOpen_ball : IsOpen (Metric.ball (0:ℂ) 1)).isOpenEmbedding_subtypeVal
    rw [discHyperbolicArea,image_iUnion,measure_iUnion
      (fun i j hij=>(Set.disjoint_image_iff Complex.UnitDisc.coe_injective).mpr (hd hij))
      (fun i=>(hcoe.isOpenMap _ (T i).interior_isOpen).measurableSet)]
    change (∑'i : Fin n,discHyperbolicArea (T i).interior)=(n:ℝ≥0∞)*ENNReal.ofReal Real.pi
    simp_rw [ClosedDiscTriangle.area_eq_pi_of_all_ideal _ (ha _) (hb _) (hc _)]
    simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hbound : (n:ℝ≥0∞)*ENNReal.ofReal Real.pi≤discHyperbolicArea S :=
    hm ▸ measure_mono (image_mono hsub)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast] using hbound

/-- The literal real-axis ideal point in the genuine compactified half-plane. -/
def realIdealHalfPlanePoint (a : ℝ) : ClosedHalfPlaneModel :=
  ⟨((a:ℂ):OnePoint ℂ),(coe_mem_closedHalfPlaneSet _).mpr (by simp)⟩

theorem realIdealHalfPlanePoint_ideal (a : ℝ) :
    (realIdealHalfPlanePoint a).val∈halfPlaneIdealBoundary :=
  (coe_mem_halfPlaneIdealBoundary _).mpr (by simp)

/-- A true line through infinity and a real ideal endpoint is the vertical line at that endpoint. -/
theorem idealFan_line_eq_vertical (L : HalfPlaneLine) (a : ℝ)
    (ha : realIdealHalfPlanePoint a∈L.closedCarrier)
    (hi : twoIdealInfiniteEndpoint∈L.closedCarrier) : L=HalfPlaneLine.vertical a := by
  obtain ⟨x,rfl⟩:=L.eq_vertical_of_infty_ideal
    ((L.closedCarrier_mem_ideal_iff _ twoIdealInfiniteEndpoint_ideal).mp hi)
  have hx:=((HalfPlaneLine.vertical x).closedCarrier_mem_ideal_iff _
    (realIdealHalfPlanePoint_ideal a)).mp ha
  rw [vertical_idealEndpoints] at hx
  change ((a:ℂ):OnePoint ℂ)∈({((x:ℂ):OnePoint ℂ),OnePoint.infty} : Set (OnePoint ℂ)) at hx
  simp only [mem_insert_iff,mem_singleton_iff,OnePoint.coe_ne_infty,or_false] at hx
  have he : a=x:=realOnePoint_injective hx
  rw [he]

/-- The actual ideal triangle with ordered real endpoints and infinity. -/
def idealIntervalHTriangle (a b : ℝ) (hab : a<b) : ClosedHTriangle where
  a:=realIdealHalfPlanePoint a
  b:=realIdealHalfPlanePoint b
  c:=twoIdealInfiniteEndpoint
  noncollinear:=by
    rintro ⟨L,ha,hb,hi⟩
    have hLa:=idealFan_line_eq_vertical L a ha hi
    have hLb:=idealFan_line_eq_vertical L b hb hi
    have he : a=b := by
      have hh:=hLa.symm.trans hLb
      cases hh
      rfl
    exact hab.ne he

theorem idealIntervalHTriangle_left_line (a b : ℝ) (hab : a<b) :
    (idealIntervalHTriangle a b hab).toDiscTriangle.sideLineB.toHalfPlane=HalfPlaneLine.vertical a := by
  let T:=(idealIntervalHTriangle a b hab).toDiscTriangle
  apply idealFan_line_eq_vertical
  · exact (T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB
  · exact (T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB

theorem idealIntervalHTriangle_right_line (a b : ℝ) (hab : a<b) :
    (idealIntervalHTriangle a b hab).toDiscTriangle.sideLineA.toHalfPlane=HalfPlaneLine.vertical b := by
  let T:=(idealIntervalHTriangle a b hab).toDiscTriangle
  apply idealFan_line_eq_vertical
  · exact (T.sideLineA.closedCarrier_cayley_mem _).mp T.b_mem_sideLineA
  · exact (T.sideLineA.closedCarrier_cayley_mem _).mp T.c_mem_sideLineA

/-- Each actual ideal interval triangle lies in its literal open real-coordinate strip. -/
theorem idealIntervalHTriangle_interior_re_bounds (a b : ℝ) (hab : a<b) :
    (idealIntervalHTriangle a b hab).toDiscTriangle.halfPlaneInterior⊆{z : ℍ | a<z.re ∧ z.re<b} := by
  let T:=(idealIntervalHTriangle a b hab).toDiscTriangle
  obtain ⟨z,hz⟩:=T.interior_nonempty
  let m:=discToHalfPlane z
  have hm : m∈T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have he:=T.halfPlaneInterior_eq_components m hm
  rw [idealIntervalHTriangle_left_line,idealIntervalHTriangle_right_line] at he
  have hsa : T.halfPlaneInterior⊆openHHalfPlane (.vertical a) m := fun _ h=>(he ▸ h).2.1
  have hsb : T.halfPlaneInterior⊆openHHalfPlane (.vertical b) m := fun _ h=>(he ▸ h).1
  have hma : m.re≠a := connectedComponentIn_subset _ _ (hsa hm)
  have hmb : m.re≠b := connectedComponentIn_subset _ _ (hsb hm)
  have hcl (p : ClosedHalfPlaneModel) (hp : p.val∈halfPlaneIdealBoundary)
      (hpT : closedModelCayleyHomeomorph p∈T.closedCarrier) :
      p.val∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) := by
    have hh:=(T.idealPoint_mem_traceInterior _ hpT (closedModelCayley_ideal_norm p hp)).1
    rw [closedModelCayley_toExtended,extendedCayley.symm_apply_apply] at hh
    exact hh
  have ha : (((a:ℝ):ℂ):OnePoint ℂ)∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) :=
    hcl _ (realIdealHalfPlanePoint_ideal a) (subset_closedDiscHConvexHull _ (by change _=T.a ∨ _=T.b ∨ _=T.c; exact Or.inl rfl))
  have hb : (((b:ℝ):ℂ):OnePoint ℂ)∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) :=
    hcl _ (realIdealHalfPlanePoint_ideal b) (subset_closedDiscHConvexHull _ (by change _=T.a ∨ _=T.b ∨ _=T.c; exact Or.inr (Or.inl rfl)))
  have hpos:=vertical_components_position_of_closure T.halfPlaneInterior (a:ℂ) (b:ℂ) hab ha hb m hma hmb hsa hsb
  intro u hu
  have huA:=hsa hu
  have huB:=hsb hu
  rw [openHHalfPlane_vertical_gt a m hpos.1] at huA
  rw [hReCutLt_eq_openHalfPlane b m hpos.2] at huB
  exact ⟨huA,huB⟩

/-- The literal real ideal trace of the actual compactified closure. -/
def realIdealClosureTrace (S : Set 𝔻) : Set ℝ :=
  {a | closedModelCayleyHomeomorph (realIdealHalfPlanePoint a)∈_root_.closure (discToClosedModel '' S)}

/-- An infinite real ideal trace, together with the genuine infinity endpoint, supplies arbitrarily many disjoint full-area ideal triangles. -/
theorem infinite_realIdealClosureTrace_area_lower_bound {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (hE : (realIdealClosureTrace S).Infinite)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S))
    (n : ℕ) : ENNReal.ofReal ((n:ℝ)*Real.pi)≤discHyperbolicArea S := by
  obtain ⟨s,hs,hcard⟩:=hE.exists_subset_card_eq (2*n)
  let e:=s.orderEmbOfFin hcard
  let l (i : Fin n) : Fin (2*n):=⟨2*i.val,by omega⟩
  let r (i : Fin n) : Fin (2*n):=⟨2*i.val+1,by omega⟩
  have hlr (i : Fin n) : e (l i)<e (r i) := e.strictMono (by change 2*i.val<2*i.val+1;omega)
  let T (i : Fin n):=(idealIntervalHTriangle (e (l i)) (e (r i)) (hlr i)).toDiscTriangle
  have hideal (i : Fin n) : ‖((T i).a:ℂ)‖=1 ∧ ‖((T i).b:ℂ)‖=1 ∧ ‖((T i).c:ℂ)‖=1 := by
    exact ⟨closedModelCayley_ideal_norm _ (realIdealHalfPlanePoint_ideal _),
      closedModelCayley_ideal_norm _ (realIdealHalfPlanePoint_ideal _),
      closedModelCayley_ideal_norm _ twoIdealInfiniteEndpoint_ideal⟩
  have hmem (i : Fin (2*n)) : e i∈realIdealClosureTrace S:=hs (s.orderEmbOfFin_mem hcard i)
  apply ideal_triangle_family_area_le hS ho hn n T
    (fun i=>(hideal i).1) (fun i=>(hideal i).2.1) (fun i=>(hideal i).2.2)
    (fun i=>hmem (l i)) (fun i=>hmem (r i)) (fun _=>hi)
  intro i j hij
  apply disjoint_left.mpr
  intro z hzi hzj
  have hzH (k : Fin n) (hz : z∈(T k).interior) : discToHalfPlane z∈(T k).halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈(T k).interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hiB:=idealIntervalHTriangle_interior_re_bounds _ _ (hlr i) (hzH i hzi)
  have hjB:=idealIntervalHTriangle_interior_re_bounds _ _ (hlr j) (hzH j hzj)
  rcases lt_or_gt_of_ne hij with hlt|hlt
  · have horder : e (r i)<e (l j):=e.strictMono (by change 2*i.val+1<2*j.val;have:=hlt;change i.val < j.val at this;omega)
    linarith [hiB.2,hjB.1]
  · have horder : e (r j)<e (l i):=e.strictMono (by change 2*j.val+1<2*i.val;have:=hlt;change j.val < i.val at this;omega)
    linarith [hjB.2,hiB.1]

/-- Infinitely many literal real ideal closure points force infinite genuine density area when infinity is also an actual ideal closure point. -/
theorem infinite_realIdealClosureTrace_area_top {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (hE : (realIdealClosureTrace S).Infinite)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S)) :
    discHyperbolicArea S=⊤ := by
  by_contra hfin
  obtain ⟨n,hnlarge⟩:=exists_nat_gt ((discHyperbolicArea S).toReal/Real.pi)
  have hb:=infinite_realIdealClosureTrace_area_lower_bound hS ho hn hE hi n
  have he:=(ENNReal.ofReal_le_iff_le_toReal hfin).mp hb
  have hgt : (discHyperbolicArea S).toReal<(n:ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hnlarge
  exact (not_lt_of_ge he) hgt

/-- The actual finite and compactified determinant-one action used to normalize a genuine ideal endpoint. -/
def idealFanSLIsometry (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ClosedDiscIsometry where
  finiteMap:=discSL2Equiv s
  distance_eq:=discSL2Equiv_distance s
  closedMap:=closedModelCayleyHomeomorph.symm.trans
    ((realGLClosedHalfPlaneHomeomorph (Matrix.SpecialLinearGroup.mapGL ℝ s) (by simp)).trans
      closedModelCayleyHomeomorph)
  finite_commutes:=by
    intro z
    have hz : closedModelCayleyHomeomorph.symm (discToClosedModel z)=halfPlaneToClosedModel (discToHalfPlane z) := by
      apply closedModelCayleyHomeomorph.injective
      rw [closedModelCayleyHomeomorph.apply_symm_apply,closedModelCayley_on_interior,halfPlaneToDisc_discToHalfPlane]
    change closedModelCayleyHomeomorph
      (realGLClosedHalfPlaneHomeomorph _ _ (closedModelCayleyHomeomorph.symm (discToClosedModel z)))=_
    rw [hz,realGLClosedHalfPlaneHomeomorph_finite,closedModelCayley_on_interior]
    rfl

/-- The literal ideal portion of the genuine compactified closure of a native region. -/
def discIdealClosureTrace (S : Set 𝔻) : Set 𝕔𝔻 :=
  {p | p∈_root_.closure (discToClosedModel '' S) ∧ ‖(p:ℂ)‖=1}

/-- A genuine closed-model isometry transports exactly the actual ideal closure points. -/
theorem ClosedDiscIsometry.image_discIdealClosureTrace (e : ClosedDiscIsometry) (S : Set 𝔻) :
    e.closedMap '' discIdealClosureTrace S=discIdealClosureTrace (e.finiteMap '' S) := by
  have he : e.closedMap '' _root_.closure (discToClosedModel '' S)=
      _root_.closure (discToClosedModel '' (e.finiteMap '' S)) := by
    rw [e.closedMap.image_closure,e.closedMap_image_finite]
  ext p
  constructor
  · rintro ⟨q,⟨hq,hi⟩,rfl⟩
    exact ⟨he ▸ mem_image_of_mem e.closedMap hq,(e.ideal_iff q).mpr hi⟩
  · rintro ⟨hp,hi⟩
    obtain ⟨q,hq,rfl⟩:=he.symm ▸ hp
    exact ⟨q,⟨hq,(e.ideal_iff q).mp hi⟩,rfl⟩

/-- The inverse genuine Cayley coordinate of an ideal point is on the literal real-axis/infinity boundary. -/
theorem discIdealPoint_halfPlaneCoordinate (p : 𝕔𝔻) (hp : ‖(p:ℂ)‖=1) :
    (closedModelCayleyHomeomorph.symm p).val∈halfPlaneIdealBoundary := by
  rw [idealBoundary_cayley_iff,←closedModelCayley_toExtended,closedModelCayleyHomeomorph.apply_symm_apply]
  exact (coe_mem_extendedDiscIdealBoundary _).mpr hp

/-- A true ideal point is either the Cayley infinity endpoint or the Cayley image of one literal real point. -/
theorem discIdealPoint_real_or_infty (p : 𝕔𝔻) (hp : ‖(p:ℂ)‖=1) :
    p=closedModelCayleyHomeomorph twoIdealInfiniteEndpoint ∨
      ∃a : ℝ,p=closedModelCayleyHomeomorph (realIdealHalfPlanePoint a) := by
  have hh:=discIdealPoint_halfPlaneCoordinate p hp
  rcases hh with he|⟨z,hz,he⟩
  · left
    apply closedModelCayleyHomeomorph.symm.injective
    rw [closedModelCayleyHomeomorph.symm_apply_apply]
    exact Subtype.ext he
  · right
    refine ⟨z.re,?_⟩
    apply closedModelCayleyHomeomorph.symm.injective
    rw [closedModelCayleyHomeomorph.symm_apply_apply]
    apply Subtype.ext
    change (closedModelCayleyHomeomorph.symm p).val=((z.re:ℂ):OnePoint ℂ)
    rw [←he]
    congr 1
    apply Complex.ext
    · rfl
    · simpa using hz

/-- Every true ideal point can actually be moved to infinity by a determinant-one isometry. -/
theorem discIdealPoint_exists_SL_normalizer (p : 𝕔𝔻) (hp : ‖(p:ℂ)‖=1) :
    ∃s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (idealFanSLIsometry s).closedMap p=closedModelCayleyHomeomorph twoIdealInfiniteEndpoint := by
  obtain ⟨s,hs⟩:=halfPlaneIdealBoundary_exists_sl2_to_infty
    (closedModelCayleyHomeomorph.symm p).val (discIdealPoint_halfPlaneCoordinate p hp)
  refine ⟨s,?_⟩
  change closedModelCayleyHomeomorph
    ((realGLClosedHalfPlaneHomeomorph _ _) (closedModelCayleyHomeomorph.symm p))=_
  congr 1
  exact Subtype.ext hs

/-- Infinite genuine ideal trace gives infinitely many real ideal points after removing its single infinity point. -/
theorem infinite_realIdealClosureTrace_of_infinite {S : Set 𝔻}
    (hE : (discIdealClosureTrace S).Infinite) : (realIdealClosureTrace S).Infinite := by
  intro hf
  apply hE
  apply ((hf.image (fun a=>closedModelCayleyHomeomorph (realIdealHalfPlanePoint a))).insert
    (closedModelCayleyHomeomorph twoIdealInfiniteEndpoint)).subset
  intro p hp
  rcases discIdealPoint_real_or_infty p hp.2 with he|⟨a,he⟩
  · exact Or.inl he
  · apply mem_insert_of_mem
    refine ⟨a,?_,he.symm⟩
    change closedModelCayleyHomeomorph (realIdealHalfPlanePoint a)∈_root_.closure (discToClosedModel '' S)
    rw [←he]
    exact hp.1

/-- Infinite actual ideal boundary forces infinite true hyperbolic density area in every nonempty open convex region. -/
theorem DiscHConvex.area_top_of_infinite_idealClosureTrace {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (hE : (discIdealClosureTrace S).Infinite) :
    discHyperbolicArea S=⊤ := by
  obtain ⟨p,hp⟩:=hE.nonempty
  obtain ⟨s,hs⟩:=discIdealPoint_exists_SL_normalizer p hp.2
  let e:=idealFanSLIsometry s
  let S':=e.finiteMap '' S
  have htrace : (discIdealClosureTrace S').Infinite := by
    rw [←e.image_discIdealClosureTrace S]
    exact hE.image e.closedMap.injective.injOn
  have hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S') := by
    have hmem : e.closedMap p∈discIdealClosureTrace S' := by
      rw [←e.image_discIdealClosureTrace S]
      exact mem_image_of_mem _ hp
    rw [show e.closedMap p=closedModelCayleyHomeomorph twoIdealInfiniteEndpoint from hs] at hmem
    exact hmem.1
  have hc : DiscHConvex S' := by
    let := discHyperbolicMetric
    apply hS.isometry_image
    apply Isometry.of_dist_eq
    intro x y
    rw [discHyperbolicMetric_distance,discHyperbolicMetric_distance]
    change discPathDist (discSL2Equiv s x) (discSL2Equiv s y)=discPathDist x y
    exact discSL2Equiv_distance s x y
  have ho' : IsOpen S' := (discSL2Homeomorph s).isOpenMap S ho
  have hn' : S'.Nonempty := hn.image e.finiteMap
  have htop:=infinite_realIdealClosureTrace_area_top hc ho' hn'
    (infinite_realIdealClosureTrace_of_infinite htrace) hi
  change discHyperbolicArea (discSL2Equiv s '' S)=⊤ at htop
  rwa [discSL2Equiv_area s S ho.measurableSet] at htop

/-- A nonempty open h-convex region of finite genuine density area has only finitely many actual ideal closure points. -/
theorem DiscHConvex.idealClosureTrace_finite_of_area_ne_top {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤) :
    (discIdealClosureTrace S).Finite := by
  by_contra hi
  exact harea (hS.area_top_of_infinite_idealClosureTrace ho hn hi)

/-- The compactified ideal trace is exactly the usual complex closure intersected with the unit circle. -/
theorem discIdealClosureTrace_coe_image (S : Set 𝔻) :
    ((↑) : 𝕔𝔻→ℂ) '' discIdealClosureTrace S=
      _root_.closure (((↑) : 𝔻→ℂ) '' S) ∩ Metric.sphere (0:ℂ) 1 := by
  have hcl (p : 𝕔𝔻) : p∈_root_.closure (discToClosedModel '' S) ↔
      (p:ℂ)∈_root_.closure (((↑) : 𝔻→ℂ) '' S) := by
    rw [Complex.UnitClosedDisc.isEmbedding_coe.closure_eq_preimage_closure_image]
    simp only [image_image]
    rfl
  ext z
  constructor
  · rintro ⟨p,⟨hp,hi⟩,rfl⟩
    exact ⟨(hcl p).mp hp,by simpa only [Metric.mem_sphere,dist_zero_right] using hi⟩
  · rintro ⟨hz,hi⟩
    have hn : ‖z‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using hi
    let p:=Complex.UnitClosedDisc.mk z hn.le
    exact ⟨p,⟨(hcl p).mpr hz,hn⟩,rfl⟩

/-- The genuine compactified ideal boundary is finite even when the convex region is empty. -/
theorem DiscHConvex.idealClosureTrace_finite {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (harea : discHyperbolicArea S≠⊤) : (discIdealClosureTrace S).Finite := by
  by_cases hn : S.Nonempty
  · exact hS.idealClosureTrace_finite_of_area_ne_top ho hn harea
  · rw [not_nonempty_iff_eq_empty] at hn
    subst S
    simp only [discIdealClosureTrace,image_empty,_root_.closure_empty,mem_empty_iff_false,false_and,
      ofPred_false,finite_empty]

/-- Finite genuine density area forces finitely many literal unit-circle closure points, with no extra boundary hypothesis. -/
theorem DiscHConvex.complexIdealBoundary_finite {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (harea : discHyperbolicArea S≠⊤) :
    (_root_.closure (((↑) : 𝔻→ℂ) '' S) ∩ Metric.sphere (0:ℂ) 1).Finite := by
  rw [←discIdealClosureTrace_coe_image]
  exact (hS.idealClosureTrace_finite ho harea).image _

end LowDimensionalTopology.Geometry.Hyperbolic
