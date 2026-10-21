module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePolygonRegularity
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareIncidentChambers
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeDihedralChambers
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) P)

/-- Actual reflection-side data fix every literal original side point. -/
theorem native_reflection_sides_fixed
    (hs : ∀s : P.Side,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s.val⊆L.carrier ∧ S.element
      s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L) :
    ∀s : P.Side,∀z∈s.val,S.generator s • z=z := by
  intro s z hz
  obtain ⟨L,hL,hE⟩ := hs s
  change (S.element s) z=z
  rw [hE]
  exact (L.reflection_fixed_iff z).mpr (hL hz)

/-- The true incident subgroup is the original two-reflection group when precisely those two
actual sides meet at the original vertex. -/
theorem native_incident_reflection_pair (x : P.Point) (s t : P.Side)
    (hs : x.val∈s.val) (ht : x.val∈t.val)
    (hAll : ∀u : P.Side,x.val∈u.val →u=s ∨ u=t)
    (R Q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt x.val)
    (hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine)
    (hQ : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine) :
    (S.incidentSubgroup x).map S.Generated.subtype=
      Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine}:Set (ℍ ≃ᵢ ℍ)) := by
  rw [S.incidentSubgroup_map]
  congr 1
  ext g
  constructor
  · rintro ⟨u,hu,rfl⟩
    rcases hAll u hu with rfl | rfl
    · exact Or.inl hR
    · exact Or.inr hQ
  · rintro (hg | hg)
    · exact ⟨s,hs,hg.trans hR.symm⟩
    · exact ⟨t,ht,hg.trans hQ.symm⟩

/-- An original reciprocal-angle reflection vertex has a finite whole original gluing class;
no finiteness of the incident group or quotient class is assumed. -/
theorem native_integral_reflection_vertex_fiber_finite
    (hself : ∀s : P.Side,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s.val⊆L.carrier ∧
      S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L)
    (x : P.Point) (s t : P.Side)
    (hs : x.val∈s.val) (ht : x.val∈t.val)
    (hAll : ∀u : P.Side,x.val∈u.val →u=s ∨ u=t)
    (R Q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt x.val)
    (hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine)
    (hQ : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine)
    (n : ℕ) (hn : 2≤n) (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R
      Q=Real.pi/(n:ℝ)) :
    (S.project ⁻¹' {S.project (1,x)}).Finite := by
  let K := Subgroup.closure ({
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine}:Set (ℍ ≃ᵢ ℍ))
  let : Finite K := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_reflections_finite_of_angle R Q n hn
    hangle).to_subtype
  let : Finite (S.incidentSubgroup x) := S.finite_incidentSubgroup_of_finite_ambient x K (by
    intro u hu
    rcases hAll u hu with rfl | rfl
    · exact Subgroup.subset_closure (Or.inl hR)
    · exact Subgroup.subset_closure (Or.inr hQ))
  exact S.finite_project_fiber_of_finite_incidentSubgroup (S.native_reflection_sides_fixed hself) x

/--
The genuine reciprocal-angle chamber geometry yields all local local tessellation balls for an arbitrary
original reflection polygon vertex. The actual closed-side local finiteness supplies side avoidance.
-/
theorem native_integral_reflection_vertex_local_radius
    (hself : ∀s : P.Side,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s.val⊆L.carrier ∧
      S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L)
    (hLF : LocallyFinite (fun s : P.Side=>s.val)) (hClosed : ∀s : P.Side,IsClosed s.val)
    (x : P.Point) (s t : P.Side) (R Q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt x.val)
    (hAll : ∀u : P.Side,x.val∈u.val →u=s ∨ u=t)
    (hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine)
    (hQ : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine)
    (hs : s.val=P.carrier∩R.supportLine.carrier) (ht : t.val=P.carrier∩Q.supportLine.carrier)
    (hProper : R.supportLine≠Q.supportLine)
    (hGerm : ∃r : ℝ,0<r ∧ ∀z : ℍ,dist z x.val<r →
      (z∈P.carrier ↔ z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R Q)))
    (n : ℕ) (hn : 2≤n) (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R
      Q=Real.pi/(n:ℝ)) :
    ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ → S.LocalTessellation (1,x) r := by
  let : IsIsometricSMul S.Generated ℍ :=
    ⟨fun g=>g.val.isometry⟩
  obtain ⟨r,hr,hG⟩ := hGerm
  obtain ⟨a,ha,hAvoid⟩ := exists_ball_incident_sides hLF hClosed x
  let δ:=min r a
  have hδ : 0<δ:=lt_min hr ha
  have hBallGerm (z : ℍ) (hz : dist z x.val<δ) :
      z∈P.carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R
        Q) := hG z (hz.trans_le (min_le_left _ _))
  have hxs : x.val∈s.val := by rw [hs];exact ⟨x.property,R.start_mem_support⟩
  have hxt : x.val∈t.val := by rw [ht];exact ⟨x.property,Q.start_mem_support⟩
  have hK := S.native_incident_reflection_pair x s t hxs hxt hAll R Q hR hQ
  have hMem (g : S.Generated) (hg : g∈S.incidentSubgroup x) :
      g.val∈Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry Q.supportLine}:Set (ℍ ≃ᵢ ℍ)) := by
    rw [←hK]
    exact ⟨g,hg,rfl⟩
  apply S.local_radius_of_incident_chamber (S.native_reflection_sides_fixed hself) x δ hδ
  · intro p hp u hpu
    exact hAvoid p.val (hp.trans_le (min_le_right _ _)) u hpu
  · intro z hz
    obtain ⟨g,hg,p,hp,hpd,hgp⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_ball_cover R Q hProper n hn hangle δ z hz
    have hgMap : g∈(S.incidentSubgroup x).map S.Generated.subtype := by rw [hK];exact hg
    obtain ⟨b,hb,hbg⟩ := hgMap
    refine ⟨b,hb,⟨p,(hBallGerm p hpd).mpr hp⟩,hpd,?_⟩
    change b.val p=z
    change b.val=g at hbg
    rw [hbg]
    exact hgp
  · intro g hg p q hp hq hpq
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_orbit_unique R Q hProper n hn hangle g.val (hMem g hg)
      p.val q.val ((hBallGerm p.val hp).mp p.property) ((hBallGerm q.val hq).mp q.property) hpq
  · intro p hp g hg hfix
    have hcases := _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_stabilizer R Q hProper n hn hangle g.val (hMem g hg)
      p.val ((hBallGerm p.val hp).mp p.property) hfix
    rcases hcases with hvertex | hone | hMR | hMQ
    · have hpx : p=x := Subtype.ext hvertex
      rwa [hpx]
    · have hg1 : g=1 := Subtype.ext hone
      rw [hg1]
      exact (S.incidentSubgroup p).one_mem
    · have hLine : p.val∈R.supportLine.carrier := by
        apply (R.supportLine.reflection_fixed_iff p.val).mp
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
          R.supportLine) p.val=p.val
        rw [←hMR]
        exact hfix
      have hps : p.val∈s.val := by rw [hs];exact ⟨p.property,hLine⟩
      have hgS : g=S.generator s := Subtype.ext (hMR.trans hR.symm)
      rw [hgS]
      exact S.generator_mem_incidentSubgroup p s hps
    · have hLine : p.val∈Q.supportLine.carrier := by
        apply (Q.supportLine.reflection_fixed_iff p.val).mp
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
          Q.supportLine) p.val=p.val
        rw [←hMQ]
        exact hfix
      have hpt : p.val∈t.val := by rw [ht];exact ⟨p.property,hLine⟩
      have hgT : g=S.generator t := Subtype.ext (hMQ.trans hQ.symm)
      rw [hgT]
      exact S.generator_mem_incidentSubgroup p t hpt

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
