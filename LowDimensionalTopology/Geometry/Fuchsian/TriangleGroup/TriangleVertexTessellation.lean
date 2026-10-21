module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexCharts
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexGerms
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralVertexFibers
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareIncidentChambers
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
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
open scoped UpperHalfPlane

/-- The actual vertex incident group is exactly the originally generated adjacent mirror pair. -/
theorem triangleVertex_incident_ambient_pair
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) :
    ((finiteTrianglePoincarePairing T).incidentSubgroup (finiteTrianglePoincareVertex T i)).map
      (finiteTrianglePoincarePairing T).Generated.subtype=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (triangleVertexFirstRay T i).supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (triangleVertexSecondRay T i).supportLine}:Set (ℍ ≃ᵢ ℍ)) := by
  rw [finiteTriangle_vertex_incident_map,triangleVertexFirstRay_support,triangleVertexSecondRay_support]
  congr 1
  ext a
  constructor
  · rintro ⟨j,hj,rfl⟩
    rcases (triangleVertex_incident_sides i j).mp hj with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl|he)
    · refine ⟨triangleVertexFirstSide i,?_,rfl⟩
      exact (triangleVertex_incident_sides i _).mpr (Or.inl rfl)
    · refine ⟨triangleVertexSecondSide i,?_,mem_singleton_iff.mp he⟩
      exact (triangleVertex_incident_sides i _).mpr (Or.inr rfl)

/-- The two actual finite triangle corner rays have distinct full supports. -/
theorem triangleVertex_rays_proper (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    (triangleVertexFirstRay T i).supportLine≠(triangleVertexSecondRay T i).supportLine := by
  fin_cases i
  · exact T.proper_angleA
  · exact T.proper_angleB
  · exact T.proper_angleC

/-- The genuine finite reciprocal-angle vertex chamber supplies the full original local local tessellation radius. -/
theorem finiteTriangle_integral_vertex_local_radius
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3)
    (n : ℕ) (hn : 2≤n) (hangle : triangleVertexAngle T i=Real.pi/(n:ℝ)) :
    ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r≤r₀ →
      (finiteTrianglePoincarePairing T).LocalTessellation (1,finiteTrianglePoincareVertex T i) r := by
  let S:=finiteTrianglePoincarePairing T
  let v:=finiteTrianglePoincareVertex T i
  let R:=triangleVertexFirstRay T i
  let Q:=triangleVertexSecondRay T i
  have hθ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R Q=Real.pi/(n:ℝ):=(triangleVertex_rays_angle T i).trans hangle
  have hProper : R.supportLine≠Q.supportLine:=triangleVertex_rays_proper T i
  let : IsIsometricSMul S.Generated ℍ:=
    (finiteTrianglePoincare_metric_assumptions T).generatedIsometricSMul S
  obtain ⟨r,hr,hGerm⟩:=triangleVertex_local_closed_germ T i
  obtain ⟨t,ht,hMiss⟩:=triangleVertex_misses_opposite_side T i
  let δ:=min r t
  have hδ : 0<δ:=lt_min hr ht
  have hBallGerm (x : ℍ) (hx : dist x v.val<δ) :
      x∈(finiteTrianglePoincarePolygon T).carrier ↔ x∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R Q):=
    hGerm x (hx.trans_le (min_le_left r t))
  have hK:=triangleVertex_incident_ambient_pair T i
  have hMem (g : S.Generated) (hg : g∈S.incidentSubgroup v) :
      g.val∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry R.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry Q.supportLine}:Set (ℍ ≃ᵢ ℍ)):=by
    rw [←hK]
    exact ⟨g,hg,rfl⟩
  apply S.local_radius_of_incident_chamber (finiteTriangle_fixed_sides T) v δ hδ
  · intro x hx s hxs
    let j:=(finiteTrianglePoincareSideEquiv T).symm s
    have hxj : x.val∈finiteTrianglePoincareSide T j:=by
      rwa [finiteTrianglePoincareSideEquiv_symm]
    have hji : j≠i:=by
      intro he
      rw [he] at hxj
      exact hMiss x.val (hx.trans_le (min_le_right r t)) hxj
    have hvj : v.val∈finiteTrianglePoincareSide T j:=
      (finiteTriangle_vertex_mem_side T i j).mpr (Ne.symm hji)
    rwa [finiteTrianglePoincareSideEquiv_symm] at hvj
  · intro z hz
    obtain ⟨g,hg,x,hx,hxr,hgx⟩:=triangleVertex_closed_angle_ball_cover R Q hProper n hn hθ δ z hz
    have hgMap : g∈(S.incidentSubgroup v).map S.Generated.subtype:=by
      rw [hK]
      exact hg
    obtain ⟨a,ha,hag⟩:=hgMap
    let p : (finiteTrianglePoincarePolygon T).Point:=⟨x,(hBallGerm x hxr).mpr hx⟩
    refine ⟨a,ha,p,hxr,?_⟩
    change a.val x=z
    change a.val=g at hag
    rw [hag]
    exact hgx
  · intro g hg x y hx hy hxy
    exact triangleVertex_closed_angle_orbit_unique R Q hProper n hn hθ g.val (hMem g hg)
      x.val y.val ((hBallGerm x.val hx).mp x.property) ((hBallGerm y.val hy).mp y.property) hxy
  · intro x hx g hg hfix
    have hcases:=triangleVertex_closed_angle_stabilizer R Q hProper n hn hθ g.val (hMem g hg)
      x.val ((hBallGerm x.val hx).mp x.property) hfix
    rcases hcases with hvertex|hone|hR|hQ
    · have hxv : x=v:=Subtype.ext hvertex
      rwa [hxv]
    · have hg1 : g=1:=Subtype.ext hone
      rw [hg1]
      exact (S.incidentSubgroup x).one_mem
    all_goals
      have hBoundary (j : Fin 3) (he : g.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (finiteTrianglePoincareLine T j)) :
          g∈S.incidentSubgroup x:=by
        have hline : x.val∈(finiteTrianglePoincareLine T j).carrier:=by
          apply ((finiteTrianglePoincareLine T j).reflection_fixed_iff x.val).mp
          change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (finiteTrianglePoincareLine T j)) x.val=x.val
          rw [←he]
          exact hfix
        have hxj : x.val∈finiteTrianglePoincareSide T j:=
          (triangleBarycentric_side T j x.val).mpr
            ⟨x.property,(triangleBarycentric_sideLine T j x.val).mp hline⟩
        let s:=(finiteTrianglePoincareSideEquiv T) j
        have hxs : x.val∈s.val:=hxj
        have hGen : g=S.generator s:=by
          apply Subtype.ext
          exact he.trans (finiteTriangle_generator_reflection T j).symm
        rw [hGen]
        exact S.generator_mem_incidentSubgroup x s hxs
    · apply hBoundary (triangleVertexFirstSide i)
      rw [←triangleVertexFirstRay_support]
      exact hR
    · apply hBoundary (triangleVertexSecondSide i)
      rw [←triangleVertexSecondRay_support]
      exact hQ

/-- All original finite reciprocal-angle triangle points satisfy the complete Poincare local tessellation. -/
theorem finiteTriangle_integral_local_tessellation
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    (finiteTrianglePoincarePairing T).FiniteFiberLocalTessellationCondition := by
  classical
  constructor
  · exact finiteTriangle_integral_all_fibers_finite T n hn hangle
  · intro x
    by_cases hv : ∀i : Fin 3,x.val≠triangleOppositeVertex T i
    · exact (finiteTriangle_nonvertex_local_condition T x hv).2
    · push Not at hv
      obtain ⟨i,hi⟩:=hv
      have hx : x=finiteTrianglePoincareVertex T i:=Subtype.ext hi
      subst x
      apply finiteTriangle_integral_vertex_local_radius T i (n i) (hn i)
      exact hangle i

/-- The original compact reciprocal-angle triangle has a genuinely discrete native reflection group
and its literal original interior is a genuine fundamental domain. -/
theorem finiteTriangle_integral_poincare (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (n : Fin 3→ℕ)
    (hn : ∀i,2≤n i) (hangle : ∀i,finiteTriangleVertexAngle T i=Real.pi/(n i:ℝ)) :
    DiscreteTopology (finiteTrianglePoincarePairing T).Generated ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (finiteTrianglePoincarePairing T).Generated ℍ
        MeasureTheory.volume T.interior := by
  apply (finiteTrianglePoincarePairing T).native_poincare_of_compact
    (finiteTriangle_integral_local_tessellation T n hn hangle) T.interior_isOpen
    ⟨T.interior_nonempty,T.interior_isPreconnected⟩ (finiteTrianglePoincarePolygon_carrier T)
    (finiteTrianglePoincarePolygon_isCompact T)
  · exact Set.countable_range _
  · rintro s ⟨i,rfl⟩
    exact ⟨finiteTrianglePoincareLine T i,finiteTrianglePoincareSide_subset_line T i⟩

end LowDimensionalTopology.Geometry.Fuchsian
