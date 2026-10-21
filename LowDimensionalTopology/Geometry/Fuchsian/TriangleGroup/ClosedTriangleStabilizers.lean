/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleDeveloping
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.SingleMirrorGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
variable {X Γ:Type*} [Group Γ] [MulAction Γ X] {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X}

theorem fixes_iff_incident_of_evaluation_injective
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
    (hf:∀s:P.Side,∀z∈s.val,S.generator s • z=z) (hi:Function.Injective S.evaluation)
    (x:P.Point) (g:S.Generated) : g • x.val=x.val ↔g∈S.incidentSubgroup x := by
  constructor
  · intro hfix
    have he:S.evaluation (S.project (g,x))=S.evaluation (S.project (1,x)):=by
      change g • x.val=(1:S.Generated) • x.val
      simpa only [one_smul] using hfix
    exact (S.project_fiber_subset_incidentSubgroup hf x (hi he)).2
  · exact S.incidentSubgroup_fixes hf x

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem closedTriangle_evaluation_injective (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : Function.Injective (closedTrianglePoincarePairing T).evaluation := by
  have he:(closedTrianglePoincarePairing T).evaluation=closedTriangle_developingHomeomorph T ha hb hc:=
    funext (fun q=>(closedTriangle_developingHomeomorph_apply T ha hb hc q).symm)
  rw [he]
  exact (closedTriangle_developingHomeomorph T ha hb hc).injective

/-- Distinct literal closed-chamber points are never identified by any actual full triangle-group element. -/
theorem closedTriangle_closed_chamber_orbit_unique (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (x y:(closedTrianglePoincarePolygon T).Point) (g:ℍ≃ᵢℍ)
    (hg:g∈triangleReflectionGroup T) (hxy:g x.val=y.val) : x.val=y.val := by
  let S:=closedTrianglePoincarePairing T
  let gS:S.Generated:=⟨g,by rwa [closedTrianglePoincarePairing_generated]⟩
  have he:S.evaluation (S.project (gS,x))=S.evaluation (S.project (1,y)):=by
    change g x.val=(1:S.Generated) • y.val
    simpa only [one_smul] using hxy
  have hp: S.project (gS,x)=S.project (1,y):=closedTriangle_evaluation_injective T ha hb hc he
  exact S.gluing_point_eq_of_fixed_sides
    (S.native_reflection_sides_fixed (closedTrianglePoincare_native_reflection_sides T))
    ((S.project_eq_iff _ _).mp hp)

/-- The whole original native triangle stabilizer is exactly the subgroup of its actual incident side mirrors. -/
theorem closedTriangle_fixed_iff_incident_mirrors (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (x:(closedTrianglePoincarePolygon T).Point) (g:ℍ≃ᵢℍ) :
    (g∈triangleReflectionGroup T ∧g x.val=x.val) ↔
      g∈Subgroup.closure {h:ℍ≃ᵢℍ|∃i:Fin 3,x.val∈T.nativeSide i ∧
        h=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine i)} := by
  let S:=closedTrianglePoincarePairing T
  have hmap:(S.incidentSubgroup x).map S.Generated.subtype=
      Subgroup.closure {h:ℍ≃ᵢℍ|∃i:Fin 3,x.val∈T.nativeSide i ∧
        h=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine i)}:=by
    rw [S.incidentSubgroup_map]
    congr 1
    ext h
    constructor
    · rintro ⟨s,hxs,rfl⟩
      let i:=(closedTrianglePoincareSideEquiv T).symm s
      refine ⟨i,?_,rfl⟩
      exact (closedTrianglePoincareSideEquiv_symm T s).symm ▸ hxs
    · rintro ⟨i,hxi,rfl⟩
      refine ⟨closedTrianglePoincareSideEquiv T i,hxi,?_⟩
      simp only [S,closedTrianglePoincarePairing,closedTrianglePoincareElement,Equiv.symm_apply_apply]
  rw [←hmap]
  have hf:=S.native_reflection_sides_fixed (closedTrianglePoincare_native_reflection_sides T)
  have hi:=closedTriangle_evaluation_injective T ha hb hc
  constructor
  · rintro ⟨hg,hfix⟩
    let gS:S.Generated:=⟨g,by rwa [closedTrianglePoincarePairing_generated]⟩
    exact ⟨gS,(S.fixes_iff_incident_of_evaluation_injective hf hi x gS).mp hfix,rfl⟩
  · rintro ⟨gS,hgS,rfl⟩
    refine ⟨?_,(S.fixes_iff_incident_of_evaluation_injective hf hi x gS).mpr hgS⟩
    rw [←closedTrianglePoincarePairing_generated]
    exact gS.property

/-- A conformal stabilizer at a literal chamber point on at most one actual side is trivial. -/
theorem closedTriangle_conformal_one_side_stabilizer
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (x:(closedTrianglePoincarePolygon T).Point)
    (i:Fin 3) (hOne:∀j:Fin 3,x.val∈T.nativeSide j→j=i)
    (g:ℍ≃ᵢℍ) (hg:g∈triangleConformalGroup T) (hfix:g x.val=x.val) : g=1 := by
  have hmem: g∈Subgroup.closure {h:ℍ≃ᵢℍ|∃j:Fin 3,x.val∈T.nativeSide j ∧
      h=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine j)}:=
    (closedTriangle_fixed_iff_incident_mirrors T ha hb hc x g).mp ⟨hg.1,hfix⟩
  have hle:Subgroup.closure {h:ℍ≃ᵢℍ|∃j:Fin 3,x.val∈T.nativeSide j ∧
      h=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine j)}≤
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (T.nativeLine i)}:Set (ℍ≃ᵢℍ)):=by
    apply (Subgroup.closure_le _).mpr
    rintro h ⟨j,hxj,rfl⟩
    rw [hOne j hxj]
    exact Subgroup.subset_closure (mem_singleton _)
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_single_mirror_group (T.nativeLine i)).1 g (hle hmem) with hg1|hgR
  · exact hg1
  · have hConf:=hg.2
    rw [hgR] at hConf
    exact False.elim (halfPlaneLineReflectionIsometry_not_conformal (T.nativeLine i) hConf)

/-- Every nontrivial conformal stabilizer on the literal closed triangle occurs at an actual finite vertex. -/
theorem closedTriangle_conformal_fixed_point_is_vertex
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (x:(closedTrianglePoincarePolygon T).Point)
    (g:ℍ≃ᵢℍ) (hg:g∈triangleConformalGroup T) (hgn:g≠1) (hfix:g x.val=x.val) :
    ∃i:Fin 3,closedTriangleVertex T i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel x.val := by
  by_contra hn
  have hOne:∃i:Fin 3,∀j:Fin 3,x.val∈T.nativeSide j→j=i:=by
    by_cases hs:∃i:Fin 3,x.val∈T.nativeSide i
    · obtain ⟨i,hxi⟩:=hs
      refine ⟨i,?_⟩
      intro j hxj
      by_contra hji
      exact hn (closedTriangle_multiple_side_point_is_vertex T x j i hji hxj hxi)
    · exact ⟨0,fun j hj=>False.elim (hs ⟨j,hj⟩)⟩
  obtain ⟨i,hi⟩:=hOne
  exact hgn (closedTriangle_conformal_one_side_stabilizer T ha hb hc x i hi g hg hfix)

end LowDimensionalTopology.Geometry.Fuchsian
