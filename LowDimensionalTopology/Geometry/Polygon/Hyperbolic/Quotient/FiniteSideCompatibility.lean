module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeHalfPlaneComponents
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSideGerms
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FinitePolygonSideStars
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FinitePolygonVertexFlags
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareSideCompatibility
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- A genuine closed supporting cut through an actual line point is an actual closed component. -/
theorem native_support_closed_cut_component (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (m :
  ℂ) (t : ℝ) (hm : m≠0)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z)=t)
    (x : ℍ) (hx : x∈N.carrier) :
    ∃u : ℍ,u∉N.carrier ∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u={z : ℍ|inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t} := by
  have hxcl : x∈closure {z : ℍ|inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<t} := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_support_cut_closure hm t]
    exact ((hLine x).mp hx).le
  obtain ⟨u,_hu,hu⟩:=mem_closure_iff.mp hxcl univ isOpen_univ (mem_univ x)
  have huN : u∉N.carrier:=fun h=>hu.ne ((hLine u).mp h)
  exact ⟨u,huN,_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_eq_le N m t hm hLine u hu⟩

/-- An arbitrary genuine original paired side map carries its entire actual supporting h-line
onto the actual supporting h-line of its original paired side. -/
theorem finitePolygon_pairing_line_image {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) (i : Fin m) :
    (S.element (finitePolygonSideEquiv Q hf i)) '' (finitePolygonLine Q i).carrier=
      (finitePolygonLine Q ((finitePolygonSideEquiv Q hf).symm (S.paired (finitePolygonSideEquiv Q hf i)))).carrier := by
  let s:=finitePolygonSideEquiv Q hf i
  let j:=(finitePolygonSideEquiv Q hf).symm (S.paired s)
  let f:=S.element s
  have hPair : finitePolygonSide Q j=(S.paired s).val:=
    congrArg Subtype.val ((finitePolygonSideEquiv Q hf).apply_symm_apply (S.paired s))
  have hImage : f '' finitePolygonSide Q i=finitePolygonSide Q j := by
    rw [hPair]
    exact S.side_image s
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine f.isometry (finitePolygonLine Q i)
  have hl:=finitePolygonSide_left_mem Q hf i
  have hr:=finitePolygonSide_right_mem Q hf i
  have hleftM : f (finitePolygonVertex Q hf i)∈M.carrier := by
    rw [←hM]
    exact mem_image_of_mem f (finitePolygonSide_subset_line Q i hl)
  have hrightM : f (finitePolygonVertex Q hf (finRotate m i))∈M.carrier := by
    rw [←hM]
    exact mem_image_of_mem f (finitePolygonSide_subset_line Q i hr)
  have hleftJ : f (finitePolygonVertex Q hf i)∈(finitePolygonLine Q j).carrier := by
    apply finitePolygonSide_subset_line Q j
    rw [←hImage]
    exact mem_image_of_mem f hl
  have hrightJ : f (finitePolygonVertex Q hf (finRotate m i))∈(finitePolygonLine Q j).carrier := by
    apply finitePolygonSide_subset_line Q j
    rw [←hImage]
    exact mem_image_of_mem f hr
  have hEq:=M.eq_of_two_points (finitePolygonLine Q j)
    (f.injective.ne ((finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm))
    hleftM hrightM hleftJ hrightJ
  rwa [hEq] at hM

/-- Actual paired-side maps preserve being a nonvertex point of the original side. -/
theorem finitePolygon_pairing_nonvertex {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (i : Fin m) {x : ℍ} (hx : x∈finitePolygonSide Q i)
    (hv : x∉range (finitePolygonVertex Q hf)) :
    S.element (finitePolygonSideEquiv Q hf i) x∉range (finitePolygonVertex Q hf) := by
  let s:=finitePolygonSideEquiv Q hf i
  have hy : S.element s x∈(S.paired s).val := by
    rw [←S.side_image]
    exact ⟨x,hx,rfl⟩
  rintro ⟨j,hj⟩
  have hjSide : finitePolygonVertex Q hf j∈(S.paired s).val:=hj.symm ▸ hy
  obtain ⟨k,hk⟩:=finitePolygonPairing_preserves_vertices Q hf S j (S.paired s) hjSide
  rw [S.element_paired,hj] at hk
  change finitePolygonVertex Q hf k=(S.element s).symm ((S.element s) x) at hk
  rw [(S.element s).symm_apply_apply] at hk
  exact hv ⟨k,hk⟩

/-- The actual original nonvertex closed-carrier germ is one of the genuine components
of the original supporting h-line complement. -/
theorem finitePolygon_nonvertex_component_germ {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) {i : Fin m} {x : ℍ}
    (hx : x∈finitePolygonSide Q i) (hv : x∉range (finitePolygonVertex Q hf)) :
    ∃u : ℍ,u∉(finitePolygonLine Q i).carrier ∧∃r : ℝ,0<r ∧∀w : ℍ,dist w x<r →
      (w∈(finiteDiscPoincarePolygon Q hf).carrier ↔w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (finitePolygonLine Q i) u) := by
  obtain ⟨m₀,t₀,hm,hLine,r,hr,hG⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_nonvertex_halfPlane_germ Q hf hx hv
  obtain ⟨u,hu,hCut⟩:=native_support_closed_cut_component (finitePolygonLine Q i) m₀ t₀ hm hLine x
    (finitePolygonSide_subset_line Q i hx)
  refine ⟨u,hu,r,hr,?_⟩
  intro w hw
  rw [hCut]
  exact hG w hw

/-- An actual closed h-line component never contains an ambient neighborhood of a point on the line. -/
theorem native_closed_halfPlane_not_nhds (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u x : ℍ)
    (hu : u∉N.carrier) (hx : x∈N.carrier) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u∉𝓝 x := by
  obtain ⟨m,t,hm,hLine⟩:=N.klein_affine_equation
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_cases N m t hm hLine u hu with he | he
  · rw [he]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_support_closed_cut_not_nhds hm t x ((hLine x).mp hx)
  · rw [he]
    have hn:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_support_closed_cut_not_nhds (neg_ne_zero.mpr hm) (-t) x (by
      rw [inner_neg_left,(hLine x).mp hx])
    simpa only [inner_neg_left,neg_le_neg_iff] using hn

/-- At a true nonvertex side point, all other original closed sides are avoided in a small ball. -/
theorem finitePolygon_nonvertex_unique_side_near {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (x : (finiteDiscPoincarePolygon Q hf).Point) (i : Fin m)
    (hx : x.val∈finitePolygonSide Q i) (hv : x.val∉range (finitePolygonVertex Q hf)) :
    ∃r : ℝ,0<r ∧∀s : (finiteDiscPoincarePolygon Q hf).Side,∀p∈s.val,dist p x.val<r →
      s=finitePolygonSideEquiv Q hf i := by
  obtain ⟨r,hr,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  refine ⟨r,hr,?_⟩
  intro s p hp hpx
  have hxs:=hNear p hpx s hp
  obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
  by_cases hji : j=i
  · exact congrArg (finitePolygonSideEquiv Q hf) hji
  · exact (hv (finitePolygon_common_sides_vertex Q hf (fun h=>hji h.symm) hx hxs)).elim

/-- A local actual closed-half-plane germ identifies its true supporting line points with
actual original polygon boundary points, without any global convexity premise. -/
theorem finitePolygon_component_germ_boundary {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (x : ℍ) (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u :
      ℍ)
    (hu : u∉N.carrier) (r : ℝ)
    (hG : ∀w : ℍ,dist w x<r →
      (w∈(finiteDiscPoincarePolygon Q hf).carrier ↔w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane
        N u))
    {z : ℍ} (hz : dist z x<r) (hzP : z∈(finiteDiscPoincarePolygon Q hf).carrier) (hzL : z∈N.carrier) :
    z∈(finiteDiscPoincarePolygon Q hf).boundary := by
  apply hzP.resolve_left
  intro hzI
  apply native_closed_halfPlane_not_nhds N u z hu hzL
  filter_upwards [(finiteDiscPoincarePolygon_interior_isOpen Q hf).mem_nhds hzI,
    Metric.isOpen_ball.mem_nhds hz] with w hwI hwBall
  exact (hG w hwBall).mp ((finiteDiscPoincarePolygon Q hf).interior_subset_carrier hwI)


/-- The original relative-neighborhood side compatibility condition forces the actual
nonvertex paired-side half-ball condition for an arbitrary original Jordan polygon. -/
theorem finitePolygon_oppositeSideNeighborhoods_paired {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (x : (finiteDiscPoincarePolygon Q hf).Point) (i : Fin m)
    (hx : x.val∈finitePolygonSide Q i) (hv : x.val∉range (finitePolygonVertex Q hf))
    (hOpp : S.OppositeSideNeighborhoods (finitePolygonSideEquiv Q hf i) x.val) :
    ∃r : ℝ,S.PairedSideNeighborhood x (finitePolygonSideEquiv Q hf i) r := by
  let P:=finiteDiscPoincarePolygon Q hf
  let s:=finitePolygonSideEquiv Q hf i
  let f:=S.element s
  let j:=(finitePolygonSideEquiv Q hf).symm (S.paired s)
  let N:=finitePolygonLine Q i
  let M:=finitePolygonLine Q j
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hPair : finitePolygonSideEquiv Q hf j=S.paired s:=
    (finitePolygonSideEquiv Q hf).apply_symm_apply (S.paired s)
  have hySide : f x.val∈finitePolygonSide Q j := by
    change f x.val∈(finitePolygonSideEquiv Q hf j).val
    rw [hPair,←S.side_image]
    exact ⟨x.val,hx,rfl⟩
  let y : P.Point:=⟨f x.val,P.side_subset_carrier (finitePolygonSideEquiv Q hf j) hySide⟩
  have hyv : y.val∉range (finitePolygonVertex Q hf):=finitePolygon_pairing_nonvertex Q hf S i hx hv
  obtain ⟨u,hu,r₀,hr₀,h₀⟩:=finitePolygon_nonvertex_component_germ Q hf hx hv
  obtain ⟨v,hvM,r₁,hr₁,h₁⟩:=finitePolygon_nonvertex_component_germ Q hf hySide hyv
  have hLines : f '' N.carrier=M.carrier:=finitePolygon_pairing_line_image Q hf S i
  let w:=f.symm v
  have hw : w∉N.carrier := by
    intro hw
    apply hvM
    rw [←hLines]
    exact ⟨w,hw,f.apply_symm_apply v⟩
  have hImage : f '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v := by
    simpa only [w,f.apply_symm_apply] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closed_halfPlane f N M hLines w hw
  have hPull (z : ℍ) : f z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w := by
    rw [←hImage]
    exact f.injective.mem_set_image
  have hActual : P.carrier∪(fun z : ℍ=>f z) ⁻¹' P.carrier∈𝓝 x.val:=
    (S.oppositeSideNeighborhoods_iff s x.val).mp hOpp
  have hComponents : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w∈𝓝 x.val := by
    filter_upwards [hActual,Metric.ball_mem_nhds x.val (lt_min hr₀ hr₁)] with z hz hzBall
    have hd₀ : dist z x.val<r₀:=lt_of_lt_of_le hzBall (min_le_left _ _)
    have hd₁ : dist (f z) y.val<r₁ := by
      change dist (f z) (f x.val)<r₁
      rw [f.isometry.dist_eq]
      exact lt_of_lt_of_le hzBall (min_le_right _ _)
    rcases hz with hz | hz
    · exact Or.inl ((h₀ z hd₀).mp hz)
    · exact Or.inr ((hPull z).mp ((h₁ (f z) hd₁).mp hz))
  obtain ⟨a,t,ha,hLine⟩:=N.klein_affine_equation
  have hIntersect : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w=N.carrier:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlanes_opposite N a t ha hLine u w x.val hu hw
      (finitePolygonSide_subset_line Q i hx) hComponents
  obtain ⟨r₂,hr₂,h₂⟩:=finitePolygon_nonvertex_unique_side_near Q hf x i hx hv
  obtain ⟨r₃,hr₃,h₃⟩:=finitePolygon_nonvertex_unique_side_near Q hf y j hySide hyv
  obtain ⟨r₄,hr₄,h₄⟩:=Metric.mem_nhds_iff.mp hActual
  let r:=min (min r₀ r₁) (min r₂ (min r₃ r₄))
  have hr : 0<r:=lt_min (lt_min hr₀ hr₁) (lt_min hr₂ (lt_min hr₃ hr₄))
  have hrr₀ : r≤r₀:=le_trans (min_le_left _ _) (min_le_left _ _)
  have hrr₁ : r≤r₁:=le_trans (min_le_left _ _) (min_le_right _ _)
  have hrr₂ : r≤r₂:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hrr₃ : r≤r₃:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrr₄ : r≤r₄:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨r,⟨hr,hx,?_,?_,?_,?_⟩⟩
  · intro a z hz hzx
    exact h₂ a z hz (lt_of_lt_of_le hzx hrr₂)
  · intro a z hz hzy
    exact (h₃ a z hz (lt_of_lt_of_le hzy hrr₃)).trans hPair
  · intro z hz
    exact h₄ (lt_of_lt_of_le hz hrr₄)
  · intro z hz hzP hzfP
    have hd₀ : dist z x.val<r₀:=lt_of_lt_of_le hz hrr₀
    have hd₁ : dist (f z) y.val<r₁ := by
      change dist (f z) (f x.val)<r₁
      rw [f.isometry.dist_eq]
      exact lt_of_lt_of_le hz hrr₁
    have hzL : z∈N.carrier := by
      rw [←hIntersect]
      exact ⟨(h₀ z hd₀).mp hzP,(hPull z).mp ((h₁ (f z) hd₁).mp hzfP)⟩
    have hzBoundary:=finitePolygon_component_germ_boundary Q hf x.val N u hu r₀ h₀ hd₀ hzP hzL
    obtain ⟨a,ha,hza⟩:=mem_sUnion.mp hzBoundary
    let a' : P.Side:=⟨a,ha⟩
    have he:=h₂ a' z hza (lt_of_lt_of_le hz hrr₂)
    exact he ▸ hza


/-- The original universal side compatibility convention gives actual regular neighborhoods
at every nonvertex point of the original finite Jordan polygon. -/
theorem finitePolygon_oppositeSideNeighborhoods_regularity {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hOpp : ∀i : Fin m,∀x∈finitePolygonSide Q i,x∉range (finitePolygonVertex Q hf) →
      S.OppositeSideNeighborhoods (finitePolygonSideEquiv Q hf i) x) :
    ∀x : (finiteDiscPoincarePolygon Q hf).Point,x.val∉range (finitePolygonVertex Q hf) →
      x.val∈(finiteDiscPoincarePolygon Q hf).interior ∨
      ∃s r,S.PairedSideNeighborhood x s r := by
  intro x hv
  rcases x.property with hx | hx
  · exact Or.inl hx
  · obtain ⟨s,hs,hxs⟩:=mem_sUnion.mp hx
    let s' : (finiteDiscPoincarePolygon Q hf).Side:=⟨s,hs⟩
    obtain ⟨i,hi⟩:=(finitePolygonSideEquiv Q hf).surjective s'
    have hxi : x.val∈finitePolygonSide Q i:=by change x.val∈(finitePolygonSideEquiv Q hf i).val;rw [hi];exact hxs
    obtain ⟨r,hr⟩:=finitePolygon_oppositeSideNeighborhoods_paired Q hf S x i hxi hv (hOpp i x.val hxi hv)
    exact Or.inr ⟨finitePolygonSideEquiv Q hf i,r,hr⟩

end LowDimensionalTopology.Geometry.Polygon
