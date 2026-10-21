/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.HalfPlaneIncenter
public import Mathlib.Analysis.Convex.StrictConvexSpace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

def ClosedHTriangle.nativeCoordinate (T : ClosedHTriangle) : ℍ→ℝ×ℝ:=T.toDiscTriangle.halfPlaneCoordinate

theorem ClosedHTriangle.nativeCoordinate_isOpenEmbedding (T : ClosedHTriangle) :
    Topology.IsOpenEmbedding T.nativeCoordinate:=T.toDiscTriangle.halfPlaneCoordinate_isOpenEmbedding

theorem ClosedHTriangle.nativeCoordinate_image_interior (T : ClosedHTriangle) :
    T.nativeCoordinate '' T.interior=standardOpenTriangle:=
  T.toDiscTriangle.halfPlaneCoordinate_image_interior

theorem ClosedHTriangle.closure_interior_coordinate (T : ClosedHTriangle) :
    closure T.interior=T.nativeCoordinate ⁻¹' standardClosedTriangle := by
  rw [T.nativeCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image,
    T.nativeCoordinate_image_interior,standardOpenTriangle_closure]

def closedTriangleFacet (i : Fin 3) : Set (ℝ×ℝ):=
  {p|p∈standardClosedTriangle ∧ ![1-p.1-p.2,p.1,p.2] i=0}

def ClosedHTriangle.nativeSide (T : ClosedHTriangle) (i : Fin 3) : Set ℍ:=
  T.nativeCoordinate ⁻¹' closedTriangleFacet i

def ClosedHTriangle.nativeLine (T : ClosedHTriangle) : Fin 3→HalfPlaneLine:=
  ![T.sideLineA,T.sideLineB,T.sideLineC]

theorem ClosedHTriangle.nativeSide_isClosed (T : ClosedHTriangle) (i : Fin 3) : IsClosed (T.nativeSide i) := by
  apply IsClosed.preimage T.nativeCoordinate_isOpenEmbedding.continuous
  change IsClosed (standardClosedTriangle∩{p:ℝ×ℝ|![1-p.1-p.2,p.1,p.2] i=0})
  apply standardClosedTriangle_isClosed.inter
  fin_cases i <;> exact isClosed_eq (by fun_prop) continuous_const

theorem ClosedHTriangle.nativeSide_eq_carrier_inter_line (T : ClosedHTriangle) (i : Fin 3) :
    T.nativeSide i=closure T.interior∩(T.nativeLine i).carrier := by
  ext z
  rw [T.closure_interior_coordinate]
  change (T.nativeCoordinate z∈standardClosedTriangle ∧ ![1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2,
    (T.nativeCoordinate z).1,(T.nativeCoordinate z).2] i=0) ↔ _
  fin_cases i
  · change (_ ∧ 1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2=0) ↔
      (_ ∧ z∈T.toDiscTriangle.sideLineA.toHalfPlane.carrier)
    rw [←T.toDiscTriangle.halfPlaneCoordinate_opposite_line]
    change (_ ∧ 1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2=0) ↔
      (_ ∧ (T.nativeCoordinate z).1+(T.nativeCoordinate z).2=1)
    constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1,by linarith⟩
  · change (_ ∧ (T.nativeCoordinate z).1=0) ↔ (_ ∧ z∈T.toDiscTriangle.sideLineB.toHalfPlane.carrier)
    rw [←T.toDiscTriangle.halfPlaneCoordinate_second_line]
    rfl
  · change (_ ∧ (T.nativeCoordinate z).2=0) ↔ (_ ∧ z∈T.toDiscTriangle.sideLineC.toHalfPlane.carrier)
    rw [←T.toDiscTriangle.halfPlaneCoordinate_first_line]
    rfl

theorem ClosedHTriangle.nativeSide_boundary (T : ClosedHTriangle) :
    ⋃₀(range T.nativeSide)=frontier T.interior := by
  ext z
  rw [frontier,T.interior_isOpen.interior_eq,T.closure_interior_coordinate]
  have hI : z∈T.interior ↔T.nativeCoordinate z∈standardOpenTriangle:=by
    rw [←T.nativeCoordinate_image_interior]
    exact T.nativeCoordinate_isOpenEmbedding.injective.mem_set_image.symm
  simp only [mem_sUnion,mem_range,exists_exists_eq_and]
  change (∃i:Fin 3,T.nativeCoordinate z∈standardClosedTriangle ∧
    ![1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2,(T.nativeCoordinate z).1,(T.nativeCoordinate z).2] i=0) ↔
    T.nativeCoordinate z∈standardClosedTriangle ∧ z∉T.interior
  rw [hI]
  simp only [Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.exists_fin_zero,or_false]
  simp only [standardClosedTriangle,standardOpenTriangle,mem_ofPred_eq]
  constructor
  · rintro (⟨h,h0⟩|⟨h,h0⟩|⟨h,h0⟩) <;> refine ⟨h,?_⟩ <;> intro hi <;> linarith [hi.1,hi.2.1,hi.2.2]
  · rintro ⟨h,hn⟩
    by_cases h0:1-(T.nativeCoordinate z).1-(T.nativeCoordinate z).2=0
    · exact Or.inl ⟨h,h0⟩
    by_cases h1:(T.nativeCoordinate z).1=0
    · exact Or.inr (Or.inl ⟨h,h1⟩)
    right;right
    refine ⟨h,?_⟩
    by_contra h2
    exact hn ⟨lt_of_le_of_ne h.1 (Ne.symm h1),lt_of_le_of_ne h.2.1 (Ne.symm h2),by
      have hSum : (T.nativeCoordinate z).1+(T.nativeCoordinate z).2≠1:=by
        intro he
        apply h0
        linarith
      exact lt_of_le_of_ne h.2.2 hSum⟩

/-- The actual closed-coordinate domain is strictly convex, including genuine ideal endpoints. -/
theorem ClosedDiscTriangle.closedCoordinateDomain_strictConvex (T : ClosedDiscTriangle) :
    StrictConvex ℝ (T.coordinateHomeomorph '' Metric.closedBall (0:ℂ) 1) := by
  change StrictConvex ℝ (T.coordinateAffine '' Metric.closedBall (0:ℂ) 1)
  exact (strictConvex_closedBall ℝ (0:ℂ) 1).affine_image T.coordinateHomeomorph.isOpenMap

theorem ClosedDiscTriangle.coordinate_mem_closedDomain (T : ClosedDiscTriangle) (p : Complex.UnitClosedDisc) :
    T.coordinate p∈T.coordinateHomeomorph '' Metric.closedBall (0:ℂ) 1 :=
  ⟨closedKleinCoordinate p,range_closedKleinCoordinate ▸ mem_range_self p,rfl⟩

/-- Every genuine edge midpoint lies inside the native open disc, even when its endpoints are ideal. -/
theorem ClosedDiscTriangle.facetMidpoint_mem_openDomain (T : ClosedDiscTriangle) (i : Fin 3) :
    ![((1/2:ℝ),1/2),(0,1/2),(1/2,0)] i∈T.openCoordinateDomain := by
  have hA:=T.coordinate_mem_closedDomain T.a
  have hB:=T.coordinate_mem_closedDomain T.b
  have hC:=T.coordinate_mem_closedDomain T.c
  rw [T.coordinate_a] at hA
  rw [T.coordinate_b] at hB
  rw [T.coordinate_c] at hC
  have hInt : _root_.interior (T.coordinateHomeomorph '' Metric.closedBall (0:ℂ) 1)=T.openCoordinateDomain:=by
    rw [←T.coordinateHomeomorph.image_interior,interior_closedBall (0:ℂ) (by norm_num : (1:ℝ)≠0)]
    rfl
  fin_cases i
  · have h:=T.closedCoordinateDomain_strictConvex hB hC (by norm_num) (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    rw [hInt] at h
    simpa using h
  · have h:=T.closedCoordinateDomain_strictConvex hC hA (by norm_num) (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    rw [hInt] at h
    simpa using h
  · have h:=T.closedCoordinateDomain_strictConvex hA hB (by norm_num) (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    rw [hInt] at h
    simpa using h

theorem ClosedHTriangle.nativeSide_nonempty (T : ClosedHTriangle) (i : Fin 3) :
    (T.nativeSide i).Nonempty := by
  have h:=T.toDiscTriangle.facetMidpoint_mem_openDomain i
  rw [←T.toDiscTriangle.halfPlaneCoordinate_range] at h
  obtain ⟨z,hz⟩:=h
  refine ⟨z,?_⟩
  change T.nativeCoordinate z∈closedTriangleFacet i
  change T.toDiscTriangle.halfPlaneCoordinate z∈closedTriangleFacet i
  rw [hz]
  fin_cases i <;> norm_num [closedTriangleFacet,standardClosedTriangle]

theorem ClosedHTriangle.nativeSide_injective (T : ClosedHTriangle) : Function.Injective T.nativeSide := by
  intro i j he
  have h:=T.toDiscTriangle.facetMidpoint_mem_openDomain i
  rw [←T.toDiscTriangle.halfPlaneCoordinate_range] at h
  obtain ⟨z,hz⟩:=h
  have hzI : z∈T.nativeSide i:=by
    change T.toDiscTriangle.halfPlaneCoordinate z∈closedTriangleFacet i
    rw [hz]
    fin_cases i <;> norm_num [closedTriangleFacet,standardClosedTriangle]
  have hzJ : z∈T.nativeSide j:=he ▸ hzI
  change T.toDiscTriangle.halfPlaneCoordinate z∈closedTriangleFacet j at hzJ
  rw [hz] at hzJ
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [closedTriangleFacet,standardClosedTriangle] at hzJ

end LowDimensionalTopology.Geometry.Hyperbolic
