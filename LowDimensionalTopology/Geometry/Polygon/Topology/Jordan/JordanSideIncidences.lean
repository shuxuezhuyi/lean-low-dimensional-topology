module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CircleNoTriod
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.ComplexJordanParametrization
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideArms
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- A true original complex Jordan curve cannot contain a triod of genuine connected
approaches. The actual unit-circle parametrization is derived from the original loop. -/
theorem complexJordan_no_three_approaches {C : Set ℂ} (hC : IsComplexJordanCurve C)
    {x : ℂ} (hx : x∈C) (A : Fin 3→Set ℂ)
    (hpre : ∀i,IsPreconnected (A i)) (hsub : ∀i,A i⊆C\{x})
    (hcl : ∀i,x∈closure (A i)) (hdis : Pairwise (fun i j=>Disjoint (A i) (A j))) : False := by
  let e:=complexJordanCircleHomeomorph hC
  let E : Circle→ℂ:=fun u=>(e u).val
  have hE : Topology.IsEmbedding E:=Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  let u:=e.symm ⟨x,hx⟩
  have hEu : E u=x:=congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  let T : Fin 3→Set Circle:=fun i=>E ⁻¹' A i
  have hImage (i : Fin 3) : E '' T i=A i := by
    apply image_preimage_eq_of_subset
    intro z hz
    exact ⟨e.symm ⟨z,(hsub i hz).1⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.circle_no_three_disjoint_preconnected_approaches u T
  · intro i
    exact hE.isInducing.isPreconnected_image.mp ((hImage i).symm ▸ hpre i)
  · intro i v hv he
    have hnot : E v≠x := (hsub i hv).2
    exact hnot (he ▸ hEu)
  · intro i
    rw [hE.closure_eq_preimage_closure_image,hImage i]
    change E u∈closure (A i)
    rw [hEu]
    exact hcl i
  · intro i j hij
    exact (hdis hij).preimage E

/-- Three distinct literal original geodesic sides cannot meet at a native point of
an actual original Jordan boundary. No valence condition is assumed. -/
theorem NativeGeodesicSideIntervals.no_three_incident_sides {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (C : Set ℂ) (hC : IsComplexJordanCurve C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (x : ℍ) (s : Fin 3→P.Side) (hsinj : Function.Injective s)
    (hx : ∀i,x∈(s i).val) : False := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hf : Continuous f:=Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hfi : Function.Injective f:=Complex.UnitDisc.coe_injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
  have hxC : f x∈C := by
    have hB : x∈P.boundary:=mem_sUnion.mpr ⟨(s 0).val,(s 0).property,hx 0⟩
    rw [hBoundary] at hB
    exact hB
  let A : Fin 3→Set ℂ:=fun i=>f '' D.openSide (s i)
  apply complexJordan_no_three_approaches hC hxC A
  · intro i
    exact (D.openSide_connected (s i)).isPreconnected.image f hf.continuousOn
  · intro i
    rintro z ⟨y,hy,rfl⟩
    have hys : y∈(s i).val:=D.openSide_closure (s i) ▸ subset_closure hy
    refine ⟨?_,?_⟩
    · have hB : y∈P.boundary:=mem_sUnion.mpr ⟨(s i).val,(s i).property,hys⟩
      rw [hBoundary] at hB
      exact hB
    · intro he
      have hyx : y=x:=hfi he
      subst y
      let j : Fin 3:=i+1
      have hij : i≠j := by fin_cases i <;>decide
      have hEnd:=D.side_intersection (s i) (s j) (hsinj.ne hij) x (hx i) (hx j)
      exact nativeCompactifiedSideInterior_no_endpoints _ _ (D.endpoint_ne (s i)) hy hEnd
  · intro i
    have hxc : x∈closure (D.openSide (s i)) := (D.openSide_closure (s i)).symm ▸ hx i
    exact hf.continuousOn.image_closure ⟨x,hxc,rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
    have hab : b=a:=hfi he
    have hb' : a∈D.openSide (s j) := by rw [←hab];exact hb
    exact Set.disjoint_left.mp (D.openSides_pairwise_disjoint (hsinj.ne hij)) ha hb'
end LowDimensionalTopology.Geometry.Polygon
