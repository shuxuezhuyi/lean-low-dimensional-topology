/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTrianglePoincareData
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FinitePolygonSideStars
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeRegularBoundaryGerms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology
  Filter
open scoped UpperHalfPlane

def closedTriangleCut (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (i : Fin 3) (z : ℍ) : ℝ:=
  ![1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2,(T.nativeCoordinate z).1,(T.nativeCoordinate z).2] i

theorem closedTriangleCut_continuous
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3) : Continuous (closedTriangleCut T i) := by
  have hF:=T.nativeCoordinate_isOpenEmbedding.continuous
  fin_cases i
  · change Continuous (fun z:ℍ=>1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2)
    fun_prop
  · change Continuous (fun z:ℍ=>(T.nativeCoordinate z).1)
    exact continuous_fst.comp hF
  · change Continuous (fun z:ℍ=>(T.nativeCoordinate z).2)
    exact continuous_snd.comp hF

theorem closedTriangle_carrier_iff_cuts
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (z : ℍ) :
    z∈(closedTrianglePoincarePolygon T).carrier ↔ ∀i,0≤closedTriangleCut T i z := by
  rw [closedTrianglePoincarePolygon_carrier,T.closure_interior_coordinate]
  change (0≤(T.nativeCoordinate z).1 ∧ 0≤(T.nativeCoordinate z).2 ∧
    (T.nativeCoordinate z).1+(T.nativeCoordinate z).2≤1) ↔ _
  simp only [Fin.forall_fin_succ,closedTriangleCut,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.forall_fin_zero,and_true]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem closedTriangle_interior_iff_cuts
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (z : ℍ) :
    z∈T.interior ↔ ∀i,0<closedTriangleCut T i z := by
  change z∈T.toDiscTriangle.halfPlaneInterior ↔ _
  rw [T.toDiscTriangle.mem_halfPlaneInterior_iff]
  simp only [Fin.forall_fin_succ,closedTriangleCut,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.forall_fin_zero,and_true,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.nativeCoordinate]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem closedTriangle_line_iff_cut_zero
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3)
    (z : ℍ) :
    z∈(T.nativeLine i).carrier ↔ closedTriangleCut T i z=0 := by
  fin_cases i
  · change z∈T.toDiscTriangle.sideLineA.toHalfPlane.carrier ↔ _
    rw [←T.toDiscTriangle.halfPlaneCoordinate_opposite_line]
    change (T.nativeCoordinate z).1+(T.nativeCoordinate z).2=1 ↔
      1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2=0
    constructor <;> intro h <;> linarith
  · exact T.toDiscTriangle.halfPlaneCoordinate_second_line z |>.symm
  · exact T.toDiscTriangle.halfPlaneCoordinate_first_line z |>.symm

theorem closedTriangle_nativeSide_iff
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i : Fin 3)
    (z : ℍ) :
    z∈T.nativeSide i ↔ z∈(closedTrianglePoincarePolygon T).carrier ∧closedTriangleCut T i z=0 := by
  rw [T.nativeSide_eq_carrier_inter_line,←closedTrianglePoincarePolygon_carrier,
    mem_inter_iff,closedTriangle_line_iff_cut_zero]

/-- At an actual point belonging to only one true side, all other original facet cuts are strictly positive. -/
theorem closedTriangle_nonvertex_other_cuts_pos (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i : Fin 3)
    (hUnique : ∀j:Fin 3,x.val∈T.nativeSide j→j=i) :
    ∀j:Fin 3,j≠i→0<closedTriangleCut T j x.val := by
  intro j hji
  have hj:=(closedTriangle_carrier_iff_cuts T x.val).mp x.property j
  apply lt_of_le_of_ne hj
  intro hz
  exact hji (hUnique j ((closedTriangle_nativeSide_iff T j x.val).mpr ⟨x.property,hz.symm⟩))

theorem closedTriangle_nonvertex_boundary_line_germ
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i : Fin 3)
    (hUnique : ∀j:Fin 3,x.val∈T.nativeSide j→j=i) :
    ∀ᶠz in 𝓝 x.val,z∈frontier T.interior ↔z∈(T.nativeLine i).carrier := by
  let U:Set ℍ:=⋂j:{j:Fin 3//j≠i},{z|0<closedTriangleCut T j.val z}
  have hU : IsOpen U:=isOpen_iInter_of_finite (fun j=>isOpen_lt continuous_const (closedTriangleCut_continuous T j.val))
  have hxU : x.val∈U:=by
    simp only [U,mem_iInter,mem_ofPred_eq]
    exact fun j=>closedTriangle_nonvertex_other_cuts_pos T x i hUnique j.val j.property
  filter_upwards [hU.mem_nhds hxU] with z hz
  have hPos (j:Fin 3) (hji:j≠i) : 0<closedTriangleCut T j z:=
    mem_iInter.mp hz ⟨j,hji⟩
  rw [closedTriangle_line_iff_cut_zero]
  constructor
  · intro hf
    have hNonneg := (closedTriangle_carrier_iff_cuts T z).mp
      ((closedTrianglePoincarePolygon_carrier T).symm ▸ frontier_subset_closure hf)
    have hnot : z∉T.interior:=(T.interior_isOpen.frontier_eq ▸ hf).2
    by_contra hn
    apply hnot
    apply (closedTriangle_interior_iff_cuts T z).mpr
    intro j
    by_cases hj:j=i
    · subst j
      exact lt_of_le_of_ne (hNonneg i) (Ne.symm hn)
    · exact hPos j hj
  · intro hzero
    rw [T.interior_isOpen.frontier_eq]
    refine ⟨?_,?_⟩
    · rw [←closedTrianglePoincarePolygon_carrier,closedTriangle_carrier_iff_cuts]
      intro j
      by_cases hj:j=i
      · subst j;rw [hzero]
      · exact (hPos j hj).le
    · intro hi
      have hh:=(closedTriangle_interior_iff_cuts T z).mp hi i
      rw [hzero] at hh
      exact lt_irrefl 0 hh

/-- The true one-side point has complete two-reflection local geometry in every finite or ideal triangle. -/
theorem closedTriangle_nonvertex_paired_neighborhood
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i : Fin 3)
    (hxi : x.val∈T.nativeSide i) (hUnique : ∀j:Fin 3,x.val∈T.nativeSide j→j=i) :
    ∃r : ℝ,(closedTrianglePoincarePairing T).PairedSideNeighborhood x (closedTrianglePoincareSideEquiv T i) r := by
  let S:=closedTrianglePoincarePairing T
  let s:=(closedTrianglePoincareSideEquiv T i)
  let N:=T.nativeLine i
  have hxF : x.val∈frontier T.interior:=by
    rw [←T.nativeSide_boundary]
    exact ⟨T.nativeSide i,mem_range_self i,hxi⟩
  obtain ⟨m,t,hm,hLine,hG⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_regular_closed_line_germ T.interior_isOpen
    (closedTriangle_regular_open T) hxF N (closedTriangle_nonvertex_boundary_line_germ T x i hUnique)
  obtain ⟨a,b,ha,hb,hab⟩:=N.exists_two_points
  obtain ⟨σ,hσ,hσG⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.native_halfPlane_signed_support N hm hab ha hb ((hLine a).mp ha) ((hLine b).mp hb)
  rw [←closedTrianglePoincarePolygon_carrier] at hG
  obtain ⟨r₀,hr₀,h₀⟩:=Metric.eventually_nhds_iff_ball.mp hG
  obtain ⟨r₁,hr₁,h₁⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.exists_ball_incident_sides (closedTrianglePoincareSide_locallyFinite T)
    (closedTrianglePoincareSide_isClosed T) x
  let r:=min r₀ r₁
  have hr : 0<r:=lt_min hr₀ hr₁
  have hP (z:ℍ) (hz:dist z x.val<r) : z∈(closedTrianglePoincarePolygon T).carrier ↔0≤σ*N.normalTimeAt z:=
    (h₀ z (hz.trans_le (min_le_left _ _))).trans (hσG z).symm
  refine ⟨r,S.pairedSideNeighborhood_of_halfPlaneReflection N hr hσ hxi ?_ rfl ?_ ?_ hP ?_⟩
  · intro z hz
    change z∈T.nativeSide i at hz
    rw [T.nativeSide_eq_carrier_inter_line] at hz
    exact hz.2
  · intro z
    change closedTrianglePoincareElement T (closedTrianglePoincareSideEquiv T i) z=N.reflection z
    simp only [closedTrianglePoincareElement,Equiv.symm_apply_apply]
    rfl
  · intro u y hy hdy
    have hxu:=h₁ y (hdy.trans_le (min_le_right _ _)) u hy
    obtain ⟨j,rfl⟩:=(closedTrianglePoincareSideEquiv T).surjective u
    exact congrArg (closedTrianglePoincareSideEquiv T) (hUnique j hxu)
  · intro z hz hn
    apply (closedTriangle_nativeSide_iff T i z).mpr
    refine ⟨(hP z hz).mpr (by rw [hn];simp),?_⟩
    exact (closedTriangle_line_iff_cut_zero T i z).mp ((N.normalTimeAt_eq_zero_iff z).mp hn)

theorem closedTriangle_nonvertex_local_condition (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (x : (closedTrianglePoincarePolygon T).Point) (i : Fin 3)
    (hxi : x.val∈T.nativeSide i) (hUnique : ∀j:Fin 3,x.val∈T.nativeSide j→j=i) :
    ((closedTrianglePoincarePairing T).project ⁻¹' {(closedTrianglePoincarePairing T).project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r≤r₀ → (closedTrianglePoincarePairing T).LocalTessellation (1,x) r := by
  let S:=closedTrianglePoincarePairing T
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  obtain ⟨r,hr⟩:=closedTriangle_nonvertex_paired_neighborhood T x i hxi hUnique
  exact ⟨hr.finite_class S,hr.local_radius S⟩

end LowDimensionalTopology.Geometry.Fuchsian
