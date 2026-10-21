/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Angles

/-! # Euclidean coordinate domains for genuine hyperbolic ray angles -/

@[expose] public section
open Set Metric Module
open scoped Topology UpperHalfPlane OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The actual two closed positive coordinate rays. -/
def positiveCoordinateAxes : Set (ℝ × ℝ) :=
  {x | (0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2)}

def positiveCoordinateQuadrant : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2}

def exteriorCoordinateQuadrant : Set (ℝ × ℝ) := {x | x.1 < 0 ∨ x.2 < 0}

theorem positiveCoordinateQuadrant_isOpen : IsOpen positiveCoordinateQuadrant :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

theorem exteriorCoordinateQuadrant_isOpen : IsOpen exteriorCoordinateQuadrant :=
  (isOpen_lt continuous_fst continuous_const).union (isOpen_lt continuous_snd continuous_const)

theorem positiveCoordinateQuadrant_convex : Convex ℝ positiveCoordinateQuadrant :=
  (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear (0 : ℝ)).inter
    (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear (0 : ℝ))

theorem coordinateAxes_complement : positiveCoordinateAxesᶜ =
    positiveCoordinateQuadrant ∪ exteriorCoordinateQuadrant := by
  ext x
  simp only [positiveCoordinateAxes,positiveCoordinateQuadrant,exteriorCoordinateQuadrant,
    mem_compl_iff,mem_ofPred,mem_union]
  grind

theorem coordinateQuadrants_disjoint : Disjoint positiveCoordinateQuadrant exteriorCoordinateQuadrant := by
  rw [disjoint_left]
  rintro x hx (hx1 | hx2)
  · exact (not_lt.mpr hx.1.le) hx1
  · exact (not_lt.mpr hx.2.le) hx2

/-- Every open neighborhood of the vertex contains actual small points in all four quadrants. -/
theorem open_domain_small_square {D : Set (ℝ × ℝ)} (hD : IsOpen D) (h0 : 0 ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ (δ,δ) ∈ D ∧ (-δ,-δ) ∈ D ∧ (-δ,2 * δ) ∈ D ∧ (2 * δ,-δ) ∈ D := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hD 0 h0
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hn1 : ‖(δ,δ)‖ < ε := by
    change max ‖δ‖ ‖δ‖ < ε
    rw [max_self,Real.norm_eq_abs,abs_of_pos hδ]
    dsimp only [δ]
    linarith
  have hn2 : ‖(-δ,-δ)‖ < ε := by
    simpa only [Prod.norm_def,norm_neg,max_self] using hn1
  have hn3 : ‖(-δ,2 * δ)‖ < ε := by
    rw [Prod.norm_def,norm_neg,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hδ,
      abs_of_pos (by positivity : 0 < 2 * δ),max_eq_right (by linarith)]
    dsimp only [δ]
    linarith
  have hn4 : ‖(2 * δ,-δ)‖ < ε := by
    simpa only [Prod.norm_def,norm_neg,max_comm] using hn3
  exact ⟨δ,hδ,hball (mem_ball_zero_iff.mpr hn1),hball (mem_ball_zero_iff.mpr hn2),
    hball (mem_ball_zero_iff.mpr hn3),hball (mem_ball_zero_iff.mpr hn4)⟩

theorem coordinateInterior_nonempty {D : Set (ℝ × ℝ)} (hD : IsOpen D) (h0 : 0 ∈ D) :
    (D ∩ positiveCoordinateQuadrant).Nonempty := by
  obtain ⟨δ,hδ,hp,_,_,_⟩ := open_domain_small_square hD h0
  exact ⟨(δ,δ),hp,hδ,hδ⟩

theorem coordinateExterior_nonempty {D : Set (ℝ × ℝ)} (hD : IsOpen D) (h0 : 0 ∈ D) :
    (D ∩ exteriorCoordinateQuadrant).Nonempty := by
  obtain ⟨δ,hδ,_,hp,_,_⟩ := open_domain_small_square hD h0
  exact ⟨(-δ,-δ),hp,Or.inl (neg_neg_of_pos hδ)⟩

theorem coordinateExterior_isPreconnected {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hconv : Convex ℝ D) (h0 : 0 ∈ D) : IsPreconnected (D ∩ exteriorCoordinateQuadrant) := by
  let A : Set (ℝ × ℝ) := D ∩ {x | x.1 < 0}
  let B : Set (ℝ × ℝ) := D ∩ {x | x.2 < 0}
  have hA : Convex ℝ A := hconv.inter (convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear 0)
  have hB : Convex ℝ B := hconv.inter (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear 0)
  obtain ⟨δ,hδ,_,hp,_,_⟩ := open_domain_small_square hD h0
  have hAB : (A ∩ B).Nonempty :=
    ⟨(-δ,-δ),⟨hp,neg_neg_of_pos hδ⟩,⟨hp,neg_neg_of_pos hδ⟩⟩
  have he : D ∩ exteriorCoordinateQuadrant = A ∪ B := by
    ext x
    change (x ∈ D ∧ (x.1 < 0 ∨ x.2 < 0)) ↔
      ((x ∈ D ∧ x.1 < 0) ∨ (x ∈ D ∧ x.2 < 0))
    tauto
  rw [he]
  exact hA.isPreconnected.union' hAB hB.isPreconnected

/-- The source exterior failure of convexity has concrete witnesses arbitrarily near the vertex. -/
theorem coordinateExterior_not_convex {D : Set (ℝ × ℝ)} (hD : IsOpen D) (h0 : 0 ∈ D) :
    ¬ Convex ℝ (D ∩ exteriorCoordinateQuadrant) := by
  obtain ⟨δ,hδ,_,_,hx,hy⟩ := open_domain_small_square hD h0
  intro hconv
  have hxE : (-δ,2 * δ) ∈ D ∩ exteriorCoordinateQuadrant := ⟨hx,Or.inl (neg_neg_of_pos hδ)⟩
  have hyE : (2 * δ,-δ) ∈ D ∩ exteriorCoordinateQuadrant := ⟨hy,Or.inr (neg_neg_of_pos hδ)⟩
  have hm := hconv.midpoint_mem hxE hyE
  have he : midpoint ℝ (-δ,2 * δ) (2 * δ,-δ) = (δ / 2,δ / 2) := by
    rw [midpoint_eq_smul_add]
    ext <;> simp <;> ring
  rw [he] at hm
  rcases hm.2 with hm | hm <;> linarith

/-- The interior is an actual component of the complement of the genuine two coordinate rays. -/
theorem connectedComponentIn_coordinateInterior {D : Set (ℝ × ℝ)}
    (hconv : Convex ℝ D) {x : ℝ × ℝ} (hx : x ∈ D ∩ positiveCoordinateQuadrant) :
    connectedComponentIn (D \ positiveCoordinateAxes) x = D ∩ positiveCoordinateQuadrant := by
  have hpart : D \ positiveCoordinateAxes =
      (D ∩ positiveCoordinateQuadrant) ∪ (D ∩ exteriorCoordinateQuadrant) := by
    rw [sdiff_eq,coordinateAxes_complement,inter_union_distrib_left]
  have hsub : D ∩ positiveCoordinateQuadrant ⊆ D \ positiveCoordinateAxes := by
    rw [hpart]
    exact subset_union_left
  apply subset_antisymm
  · have hC := isPreconnected_connectedComponentIn (F := D \ positiveCoordinateAxes) (x := x)
    have hcover : connectedComponentIn (D \ positiveCoordinateAxes) x ⊆
        positiveCoordinateQuadrant ∪ exteriorCoordinateQuadrant := by
      intro y hy
      have he := connectedComponentIn_subset _ _ hy
      rw [hpart] at he
      exact he.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    rcases IsPreconnected.subset_or_subset positiveCoordinateQuadrant_isOpen
      exteriorCoordinateQuadrant_isOpen coordinateQuadrants_disjoint hcover hC with hI | hE
    · intro y hy
      exact ⟨(connectedComponentIn_subset _ _ hy).1,hI hy⟩
    · have hxC := mem_connectedComponentIn (hsub hx)
      exact (Set.disjoint_left.mp coordinateQuadrants_disjoint hx.2 (hE hxC)).elim
  · exact (hconv.inter positiveCoordinateQuadrant_convex).isPreconnected.subset_connectedComponentIn hx hsub

/-- The exterior is the other actual connected component, rather than a formal complement label. -/
theorem connectedComponentIn_coordinateExterior {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hconv : Convex ℝ D) (h0 : 0 ∈ D) {x : ℝ × ℝ}
    (hx : x ∈ D ∩ exteriorCoordinateQuadrant) :
    connectedComponentIn (D \ positiveCoordinateAxes) x = D ∩ exteriorCoordinateQuadrant := by
  have hpart : D \ positiveCoordinateAxes =
      (D ∩ positiveCoordinateQuadrant) ∪ (D ∩ exteriorCoordinateQuadrant) := by
    rw [sdiff_eq,coordinateAxes_complement,inter_union_distrib_left]
  have hsub : D ∩ exteriorCoordinateQuadrant ⊆ D \ positiveCoordinateAxes := by
    rw [hpart]
    exact subset_union_right
  apply subset_antisymm
  · have hC := isPreconnected_connectedComponentIn (F := D \ positiveCoordinateAxes) (x := x)
    have hcover : connectedComponentIn (D \ positiveCoordinateAxes) x ⊆
        positiveCoordinateQuadrant ∪ exteriorCoordinateQuadrant := by
      intro y hy
      have he := connectedComponentIn_subset _ _ hy
      rw [hpart] at he
      exact he.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    rcases IsPreconnected.subset_or_subset positiveCoordinateQuadrant_isOpen
      exteriorCoordinateQuadrant_isOpen coordinateQuadrants_disjoint hcover hC with hI | hE
    · have hxC := mem_connectedComponentIn (hsub hx)
      exact (Set.disjoint_left.mp coordinateQuadrants_disjoint (hI hxC) hx.2).elim
    · intro y hy
      exact ⟨(connectedComponentIn_subset _ _ hy).1,hE hy⟩
  · exact (coordinateExterior_isPreconnected hD hconv h0).subset_connectedComponentIn hx hsub

/-- Actual Klein coordinate for the genuine H model. -/
def halfPlaneKleinCoordinate (z : ℍ) : ℂ := kleinCoordinate (halfPlaneToDisc z)

theorem halfPlaneKleinCoordinate_injective : Function.Injective halfPlaneKleinCoordinate :=
  kleinCoordinate_injective.comp (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)

theorem isOpenEmbedding_halfPlaneKleinCoordinate : Topology.IsOpenEmbedding halfPlaneKleinCoordinate :=
  isOpenEmbedding_kleinCoordinate.comp cayleyHomeomorph.isOpenEmbedding

theorem range_halfPlaneKleinCoordinate : range halfPlaneKleinCoordinate = Metric.ball (0 : ℂ) 1 := by
  change range (kleinCoordinate ∘ halfPlaneToDisc) = _
  have hr : range halfPlaneToDisc = univ :=
    (show Function.Surjective halfPlaneToDisc from cayleyHomeomorph.surjective).range_eq
  rw [range_comp,hr,image_univ,range_kleinCoordinate]

theorem HalfPlaneLine.klein_affine_equation (L : HalfPlaneLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧
      ∀ z : ℍ, z ∈ L.carrier ↔ inner ℝ a (halfPlaneKleinCoordinate z) = t := by
  obtain ⟨a,t,ha,hA⟩ := L.toDiscLine.exists_klein_linear_equation
  refine ⟨a,t,ha,fun z => ?_⟩
  have he : halfPlaneToDisc z ∈ L.toDiscLine.carrier ↔ z ∈ L.carrier := by
    rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
    constructor
    · rintro ⟨w,hw,he⟩
      exact (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective) he ▸ hw
    · intro hz
      exact mem_image_of_mem _ hz
  exact he.symm.trans (hA _)

/-- A concrete genuine point on each punctured ray fixes its forward direction. -/
def HRayAt.directionPoint {z : ℍ} (R : HRayAt z) : ℍ := R.punctured_nonempty.choose

theorem HRayAt.directionPoint_mem {z : ℍ} (R : HRayAt z) : R.directionPoint ∈ R.val \ {z} :=
  R.punctured_nonempty.choose_spec

def HRayAt.kleinDirection {z : ℍ} (R : HRayAt z) : ℂ :=
  halfPlaneKleinCoordinate R.directionPoint - halfPlaneKleinCoordinate z

theorem HRayAt.kleinDirection_ne_zero {z : ℍ} (R : HRayAt z) : R.kleinDirection ≠ 0 := by
  apply sub_ne_zero.mpr
  exact halfPlaneKleinCoordinate_injective.ne R.directionPoint_mem.2

/-- Two genuinely different support lines give an actual real basis of tangent-free
Klein ray directions; no independence hypothesis is added to the source angle. -/
theorem hAngleDirections_linearIndependent {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    LinearIndependent ℝ ![R.kleinDirection,S.kleinDirection] := by
  apply linearIndependent_fin2.mpr
  refine ⟨S.kleinDirection_ne_zero,?_⟩
  intro r he
  change r • S.kleinDirection = R.kleinDirection at he
  obtain ⟨a,t,_,hA⟩ := S.supportLine.klein_affine_equation
  have hzA := (hA z).mp S.start_mem_support
  have hsA := (hA S.directionPoint).mp (S.subset_support S.directionPoint_mem.1)
  have hrA : inner ℝ a (halfPlaneKleinCoordinate R.directionPoint) = t := by
    have hd : inner ℝ a R.kleinDirection = 0 := by
      rw [← he,inner_smul_right]
      change r * inner ℝ a (halfPlaneKleinCoordinate S.directionPoint - halfPlaneKleinCoordinate z) = 0
      rw [inner_sub_right,hsA,hzA,sub_self,mul_zero]
    change inner ℝ a (halfPlaneKleinCoordinate R.directionPoint - halfPlaneKleinCoordinate z) = 0 at hd
    rw [inner_sub_right,hzA] at hd
    linarith
  exact hne (R.supportLine.eq_of_two_points S.supportLine (Ne.symm R.directionPoint_mem.2)
    R.start_mem_support (R.subset_support R.directionPoint_mem.1) S.start_mem_support ((hA _).mpr hrA))

/-- The actual two ray directions form the coordinate basis. -/
def hAngleDirectionBasis {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank (hAngleDirections_linearIndependent R S hne)
    (by simp only [Fintype.card_fin,Complex.finrank_real_complex])

theorem hAngleDirectionBasis_zero {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    hAngleDirectionBasis R S hne 0 = R.kleinDirection := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 0 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem hAngleDirectionBasis_one {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    hAngleDirectionBasis R S hne 1 = S.kleinDirection := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 1 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- Genuine real linear coordinates in the two actual Klein ray directions. -/
def hAngleCoordinateLinear {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  (hAngleDirectionBasis R S hne).equivFun.trans (LinearEquiv.finTwoArrow ℝ ℝ)

def hAngleCoordinateHomeomorph {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    ℂ ≃ₜ ℝ × ℝ :=
  (Homeomorph.subRight (halfPlaneKleinCoordinate z)).trans
    (hAngleCoordinateLinear R S hne).toContinuousLinearEquiv.toHomeomorph

def hAngleCoordinate {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) (x : ℍ) : ℝ × ℝ :=
  hAngleCoordinateHomeomorph R S hne (halfPlaneKleinCoordinate x)

def hAngleCoordinateDomain {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    Set (ℝ × ℝ) := hAngleCoordinateHomeomorph R S hne '' Metric.ball (0 : ℂ) 1

theorem hAngleCoordinate_vertex {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne z = 0 := by
  change hAngleCoordinateLinear R S hne (halfPlaneKleinCoordinate z - halfPlaneKleinCoordinate z) = 0
  rw [sub_self,map_zero]

theorem hAngleCoordinate_range {z : ℍ} (R S : HRayAt z) (hne : R.supportLine ≠ S.supportLine) :
    range (hAngleCoordinate R S hne) = hAngleCoordinateDomain R S hne := by
  change range ((hAngleCoordinateHomeomorph R S hne) ∘ halfPlaneKleinCoordinate) = _
  rw [range_comp,range_halfPlaneKleinCoordinate]
  rfl

theorem hAngleCoordinate_isOpenEmbedding {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : Topology.IsOpenEmbedding (hAngleCoordinate R S hne) :=
  (hAngleCoordinateHomeomorph R S hne).isOpenEmbedding.comp isOpenEmbedding_halfPlaneKleinCoordinate

theorem hAngleCoordinateDomain_isOpen {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (hAngleCoordinateDomain R S hne) :=
  (hAngleCoordinateHomeomorph R S hne).isOpenMap _ Metric.isOpen_ball

theorem hAngleCoordinateDomain_zero_mem {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : (0 : ℝ × ℝ) ∈ hAngleCoordinateDomain R S hne := by
  rw [← hAngleCoordinate_range,← hAngleCoordinate_vertex R S hne]
  exact mem_range_self z

theorem hAngleCoordinateDomain_convex {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : Convex ℝ (hAngleCoordinateDomain R S hne) := by
  have he : hAngleCoordinateDomain R S hne = hAngleCoordinateLinear R S hne ''
      ((fun x : ℂ => -halfPlaneKleinCoordinate z + x) '' Metric.ball (0 : ℂ) 1) := by
    rw [image_image]
    apply Set.image_congr
    intro x _
    change hAngleCoordinateLinear R S hne (x - halfPlaneKleinCoordinate z) =
      hAngleCoordinateLinear R S hne (-halfPlaneKleinCoordinate z + x)
    congr 1
    abel
  rw [he]
  exact ((convex_ball (0 : ℂ) 1).translate (-halfPlaneKleinCoordinate z)).linear_image
    (hAngleCoordinateLinear R S hne).toLinearMap

theorem hAngleCoordinateLinear_first_direction {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hAngleCoordinateLinear R S hne R.kleinDirection = (1,0) := by
  rw [← hAngleDirectionBasis_zero R S hne]
  change ((hAngleDirectionBasis R S hne).equivFun (hAngleDirectionBasis R S hne 0) 0,
    (hAngleDirectionBasis R S hne).equivFun (hAngleDirectionBasis R S hne 0) 1) = (1,0)
  simp only [Basis.equivFun_self,ite_true,Fin.zero_ne_one,ite_false]

theorem hAngleCoordinateLinear_second_direction {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hAngleCoordinateLinear R S hne S.kleinDirection = (0,1) := by
  rw [← hAngleDirectionBasis_one R S hne]
  change ((hAngleDirectionBasis R S hne).equivFun (hAngleDirectionBasis R S hne 1) 0,
    (hAngleDirectionBasis R S hne).equivFun (hAngleDirectionBasis R S hne 1) 1) = (0,1)
  simp only [Basis.equivFun_self,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true]

theorem HRayAt.klein_mem_span_iff {z : ℍ} (R : HRayAt z) (x : ℍ) :
    halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z ∈ Submodule.span ℝ {R.kleinDirection} ↔
      x ∈ R.supportLine.carrier := by
  let := Complex.finrank_real_complex_fact
  obtain ⟨a,t,ha,hA⟩ := R.supportLine.klein_affine_equation
  have hzA := (hA z).mp R.start_mem_support
  have hdA := (hA R.directionPoint).mp (R.subset_support R.directionPoint_mem.1)
  have hd : inner ℝ a R.kleinDirection = 0 := by
    change inner ℝ a (halfPlaneKleinCoordinate R.directionPoint - halfPlaneKleinCoordinate z) = 0
    rw [inner_sub_right,hdA,hzA,sub_self]
  constructor
  · intro hx
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hx
    have hzero : inner ℝ a (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z) = 0 := by
      rw [← hr,inner_smul_right,hd,mul_zero]
    apply (hA x).mpr
    rw [inner_sub_right,hzA] at hzero
    linarith
  · intro hx
    have hzero : inner ℝ a (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z) = 0 := by
      rw [inner_sub_right,(hA x).mp hx,hzA,sub_self]
    exact Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha R.kleinDirection_ne_zero hzero hd

theorem linearEquiv_second_zero_iff_span (L : ℂ ≃ₗ[ℝ] ℝ × ℝ) (d : ℂ)
    (hd : L d = (1,0)) (x : ℂ) : (L x).2 = 0 ↔ x ∈ Submodule.span ℝ {d} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨(L x).1,L.injective ?_⟩
    rw [map_smul,hd]
    ext
    · simp only [Prod.smul_fst,smul_eq_mul,mul_one]
    · simp only [Prod.smul_snd,smul_eq_mul,mul_zero,hx]
  · rintro ⟨r,hr⟩
    rw [← hr,map_smul,hd]
    simp only [Prod.smul_snd,smul_eq_mul,mul_zero]

theorem linearEquiv_first_zero_iff_span (L : ℂ ≃ₗ[ℝ] ℝ × ℝ) (d : ℂ)
    (hd : L d = (0,1)) (x : ℂ) : (L x).1 = 0 ↔ x ∈ Submodule.span ℝ {d} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨(L x).2,L.injective ?_⟩
    rw [map_smul,hd]
    ext
    · simp only [Prod.smul_fst,smul_eq_mul,mul_zero,hx]
    · simp only [Prod.smul_snd,smul_eq_mul,mul_one]
  · rintro ⟨r,hr⟩
    rw [← hr,map_smul,hd]
    simp only [Prod.smul_fst,smul_eq_mul,mul_zero]

theorem hAngleCoordinate_first_support {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (x : ℍ) :
    (hAngleCoordinate R S hne x).2 = 0 ↔ x ∈ R.supportLine.carrier := by
  change (hAngleCoordinateLinear R S hne (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z)).2 = 0 ↔ _
  rw [linearEquiv_second_zero_iff_span _ _ (hAngleCoordinateLinear_first_direction R S hne),
    R.klein_mem_span_iff x]

theorem hAngleCoordinate_second_support {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (x : ℍ) :
    (hAngleCoordinate R S hne x).1 = 0 ↔ x ∈ S.supportLine.carrier := by
  change (hAngleCoordinateLinear R S hne (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z)).1 = 0 ↔ _
  rw [linearEquiv_first_zero_iff_span _ _ (hAngleCoordinateLinear_second_direction R S hne),
    S.klein_mem_span_iff x]

theorem hAngleCoordinate_first_point {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hAngleCoordinate R S hne R.directionPoint = (1,0) :=
  hAngleCoordinateLinear_first_direction R S hne

theorem hAngleCoordinate_second_point {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hAngleCoordinate R S hne S.directionPoint = (0,1) :=
  hAngleCoordinateLinear_second_direction R S hne

/-- The punctured geometric ray is the genuine component of its punctured support
containing any one of its points. -/
theorem HRayAt.punctured_eq_component {z : ℍ} (R : HRayAt z) {u : ℍ} (hu : u ∈ R.val \ {z}) :
    R.val \ {z} = connectedComponentIn (R.supportLine.carrier \ {z}) u := by
  obtain ⟨a,b,γ,s,_,_,hγ,hrange,hs,_,_,_,_⟩ := R.supportLine.exists_rays_at z R.start_mem_support
  have hor := R.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    R.ideal_mem_support γ hγ.1 hrange s hs
  have hforward : forwardHLineRay γ s \ {z} = γ '' Ioi s := by
    rw [show ({z} : Set ℍ) = {γ s} from congrArg Set.singleton hs.symm]
    ext x
    constructor
    · rintro ⟨⟨r,hr,rfl⟩,hne⟩
      have hrs : r ≠ s := fun h => hne (congrArg γ h)
      exact ⟨r,lt_of_le_of_ne hr (Ne.symm hrs),rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr.le,rfl⟩,fun h => hr.ne' (hγ.1.injective h)⟩
  have hbackward : backwardHLineRay γ s \ {z} = γ '' Iio s := by
    rw [show ({z} : Set ℍ) = {γ s} from congrArg Set.singleton hs.symm]
    ext x
    constructor
    · rintro ⟨⟨r,hr,rfl⟩,hne⟩
      have hrs : r ≠ s := fun h => hne (congrArg γ h)
      exact ⟨r,lt_of_le_of_ne hr hrs,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr.le,rfl⟩,fun h => hr.ne (hγ.1.injective h)⟩
  rcases hor with hor | hor
  · have hu' : u ∈ γ '' Ioi s := by rw [← hforward,← hor]; exact hu
    obtain ⟨r,hr,hru⟩ := hu'
    have hc := connectedComponentIn_hLine_puncturedPoint_right hγ.1 hr
    rw [hrange,hs,hru] at hc
    rw [hor,hforward,hc]
  · have hu' : u ∈ γ '' Iio s := by rw [← hbackward,← hor]; exact hu
    obtain ⟨r,hr,hru⟩ := hu'
    have hc := connectedComponentIn_hLine_puncturedPoint_left hγ.1 hr
    rw [hrange,hs,hru] at hc
    rw [hor,hbackward,hc]

/-- Open embeddings transport the actual connected components of arbitrary subsets. -/
theorem embedding_image_connectedComponentIn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsEmbedding f) {A : Set X} {x : X} (hx : x ∈ A) :
    f '' connectedComponentIn A x = connectedComponentIn (f '' A) (f x) := by
  apply subset_antisymm
  · exact hf.continuous.continuousOn.image_connectedComponentIn_subset hx
  · let C := connectedComponentIn (f '' A) (f x)
    have hCr : C ⊆ range f := (connectedComponentIn_subset _ _).trans (image_subset_range f A)
    have him : f '' (f ⁻¹' C) = C := image_preimage_eq_of_subset hCr
    have hTc : IsPreconnected (f ⁻¹' C) := by
      apply hf.isInducing.isPreconnected_image.mp
      rw [him]
      exact isPreconnected_connectedComponentIn
    have hTA : f ⁻¹' C ⊆ A := by
      intro u hu
      obtain ⟨v,hv,he⟩ := connectedComponentIn_subset _ _ hu
      exact hf.injective he ▸ hv
    have hxT : x ∈ f ⁻¹' C := mem_connectedComponentIn (mem_image_of_mem f hx)
    have hTsub := hTc.subset_connectedComponentIn hxT hTA
    intro y hy
    obtain ⟨u,heu⟩ := hCr hy
    refine ⟨u,hTsub ?_,heu⟩
    change f u ∈ C
    rw [heu]
    exact hy

/-- The genuine first positive axis is the image of the actual punctured ray,
whenever its actual support and forward witness have the specified verified coordinates. -/
theorem HRayAt.image_punctured_firstAxis {z : ℍ} (R : HRayAt z) (F : ℍ → ℝ × ℝ)
    (hF : Topology.IsEmbedding F) (hconv : Convex ℝ (range F)) (hz : F z = 0)
    (haxis : ∀ x, (F x).2 = 0 ↔ x ∈ R.supportLine.carrier)
    (htip : F R.directionPoint = (1,0)) :
    F '' (R.val \ {z}) = range F ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
  let φ : ℍ → ℝ := fun x => (F x).1
  have hφc : Continuous φ := continuous_fst.comp hF.continuous
  have hφtip : φ R.directionPoint = 1 := congrArg Prod.fst htip
  have hφne (x : ℍ) (hx : x ∈ R.val \ {z}) : φ x ≠ 0 := by
    intro he
    have hx2 := (haxis x).mpr (R.subset_support hx.1)
    have hx0 : F x = 0 := Prod.ext he hx2
    exact hx.2 (hF.injective (hx0.trans hz.symm))
  have hpos (x : ℍ) (hx : x ∈ R.val \ {z}) : 0 < φ x := by
    by_contra! hle
    have hlt : φ x < 0 := lt_of_le_of_ne hle (hφne x hx)
    have hpre := (R.punctured_isPreconnected.image φ hφc.continuousOn).ordConnected
    have htI : 1 ∈ φ '' (R.val \ {z}) := hφtip ▸ mem_image_of_mem φ R.directionPoint_mem
    obtain ⟨u,hu,he⟩ := hpre.out (mem_image_of_mem φ hx) htI
      (show (0 : ℝ) ∈ Icc (φ x) 1 from ⟨hlt.le,zero_le_one⟩)
    exact hφne u hu he
  let T : Set ℍ := F ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0}
  have him : F '' T = range F ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
    rw [image_preimage_eq_inter_range,inter_comm]
  have hTc : IsPreconnected T := by
    apply hF.isInducing.isPreconnected_image.mp
    rw [him]
    exact (hconv.inter ((convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear (0 : ℝ)).inter
      (convex_hyperplane (LinearMap.snd ℝ ℝ ℝ).isLinear (0 : ℝ)))).isPreconnected
  have hTsub : T ⊆ R.supportLine.carrier \ {z} := by
    intro x hx
    refine ⟨(haxis x).mp hx.2,?_⟩
    intro hxz
    have he : (F x).1 = 0 := by rw [hxz,hz]; rfl
    exact (ne_of_gt hx.1) he
  have htipT : R.directionPoint ∈ T := by
    change 0 < (F R.directionPoint).1 ∧ (F R.directionPoint).2 = 0
    rw [htip]
    exact ⟨zero_lt_one,rfl⟩
  have hTcomp := hTc.subset_connectedComponentIn htipT hTsub
  rw [← R.punctured_eq_component R.directionPoint_mem] at hTcomp
  apply subset_antisymm
  · rintro p ⟨x,hx,rfl⟩
    exact ⟨mem_range_self x,hpos x hx,(haxis x).mpr (R.subset_support hx.1)⟩
  · intro p hp
    rw [← him] at hp
    exact image_mono hTcomp hp

/-- Adding the vertex to the genuine punctured ray gives exactly the genuine closed coordinate half-axis. -/
theorem HRayAt.image_firstAxis {z : ℍ} (R : HRayAt z) (F : ℍ → ℝ × ℝ)
    (hF : Topology.IsEmbedding F) (hconv : Convex ℝ (range F)) (hz : F z = 0)
    (haxis : ∀ x, (F x).2 = 0 ↔ x ∈ R.supportLine.carrier)
    (htip : F R.directionPoint = (1,0)) :
    F '' R.val = range F ∩ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = 0} := by
  have hpunct := R.image_punctured_firstAxis F hF hconv hz haxis htip
  apply subset_antisymm
  · rintro p ⟨x,hx,rfl⟩
    by_cases hxz : x = z
    · rw [hxz,hz]
      exact ⟨⟨z,hz⟩,le_rfl,rfl⟩
    · have hmem := hpunct ▸ mem_image_of_mem F (show x ∈ R.val \ {z} from ⟨hx,hxz⟩)
      exact ⟨hmem.1,hmem.2.1.le,hmem.2.2⟩
  · rintro p ⟨hp,hp1,hp2⟩
    rcases eq_or_lt_of_le hp1 with hp0 | hppos
    · have hpz : p = 0 := Prod.ext hp0.symm hp2
      exact ⟨z,R.start_mem,hz.trans hpz.symm⟩
    · have hpI : p ∈ F '' (R.val \ {z}) := hpunct.symm ▸ ⟨hp,hppos,hp2⟩
      exact image_mono sdiff_subset hpI

/-- The companion genuine half-axis formula uses the actual coordinate swap homeomorphism. -/
theorem HRayAt.image_secondAxis {z : ℍ} (R : HRayAt z) (F : ℍ → ℝ × ℝ)
    (hF : Topology.IsEmbedding F) (hconv : Convex ℝ (range F)) (hz : F z = 0)
    (haxis : ∀ x, (F x).1 = 0 ↔ x ∈ R.supportLine.carrier)
    (htip : F R.directionPoint = (0,1)) :
    F '' R.val = range F ∩ {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2} := by
  let G := Prod.swap ∘ F
  have hG : Topology.IsEmbedding G := (Homeomorph.prodComm ℝ ℝ).isEmbedding.comp hF
  have hrG : range G = Prod.swap '' range F := range_comp Prod.swap F
  have hcG : Convex ℝ (range G) := by
    rw [hrG]
    exact hconv.linear_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
  have hzG : G z = 0 := by change Prod.swap (F z) = 0; rw [hz]; rfl
  have htG : G R.directionPoint = (1,0) := by change Prod.swap (F R.directionPoint) = _; rw [htip]; rfl
  have hi := R.image_firstAxis G hG hcG hzG haxis htG
  apply Prod.swap_injective.image_injective
  rw [image_image]
  change G '' R.val = _
  rw [hi,hrG,image_inter Prod.swap_injective]
  have he : Prod.swap '' {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2} =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = 0} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨hq.2,hq.1⟩
    · intro hp
      exact ⟨p.swap,⟨hp.2,hp.1⟩,Prod.swap_swap p⟩
  rw [he]

theorem hAngleCoordinate_image_firstRay {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' R.val =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = 0} := by
  have hc : Convex ℝ (range (hAngleCoordinate R S hne)) := by
    rw [hAngleCoordinate_range]
    exact hAngleCoordinateDomain_convex R S hne
  have he := R.image_firstAxis (hAngleCoordinate R S hne)
    (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding hc (hAngleCoordinate_vertex R S hne)
    (hAngleCoordinate_first_support R S hne) (hAngleCoordinate_first_point R S hne)
  rwa [hAngleCoordinate_range] at he

theorem hAngleCoordinate_image_secondRay {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' S.val =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2} := by
  have hc : Convex ℝ (range (hAngleCoordinate R S hne)) := by
    rw [hAngleCoordinate_range]
    exact hAngleCoordinateDomain_convex R S hne
  have he := S.image_secondAxis (hAngleCoordinate R S hne)
    (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding hc (hAngleCoordinate_vertex R S hne)
    (hAngleCoordinate_second_support R S hne) (hAngleCoordinate_second_point R S hne)
  rwa [hAngleCoordinate_range] at he

theorem hAngleCoordinate_image_rayUnion {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' (R.val ∪ S.val) =
      hAngleCoordinateDomain R S hne ∩ positiveCoordinateAxes := by
  rw [image_union,hAngleCoordinate_image_firstRay,hAngleCoordinate_image_secondRay,
    ← inter_union_distrib_left]
  rfl

/-- The positive side of a genuine affine hyperplane in a convex coordinate domain
is exactly its actual complement component. -/
theorem connectedComponentIn_positive_linear_cut {D : Set (ℝ × ℝ)} (hD : Convex ℝ D)
    (f : (ℝ × ℝ) →L[ℝ] ℝ) {x : ℝ × ℝ} (hx : x ∈ D ∩ {p | 0 < f p}) :
    connectedComponentIn (D ∩ {p | f p ≠ 0}) x = D ∩ {p | 0 < f p} := by
  have hsub : D ∩ {p | 0 < f p} ⊆ D ∩ {p | f p ≠ 0} :=
    fun _ hy => ⟨hy.1,ne_of_gt hy.2⟩
  apply subset_antisymm
  · intro y hy
    have hyA := connectedComponentIn_subset _ _ hy
    refine ⟨hyA.1,?_⟩
    change 0 < f y
    by_contra! hle
    have hC := (isPreconnected_connectedComponentIn
      (F := D ∩ {p | f p ≠ 0}) (x := x)).image f f.continuous.continuousOn
    have hxC := mem_connectedComponentIn (hsub hx)
    obtain ⟨v,hv,hv0⟩ := hC.ordConnected.out (mem_image_of_mem f hy)
      (mem_image_of_mem f hxC) (show (0 : ℝ) ∈ Icc (f y) (f x) from ⟨hle,hx.2.le⟩)
    exact (connectedComponentIn_subset _ _ hv).2 hv0
  · exact (hD.inter (convex_halfSpace_gt f.toLinearMap.isLinear (0 : ℝ))).isPreconnected.subset_connectedComponentIn
      hx hsub

theorem hAngleCoordinate_image_firstSide {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' hAngleSide R S =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | 0 < p.2} := by
  let F := hAngleCoordinate R S hne
  have hF := (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding
  have hcomp : F '' R.supportLine.carrierᶜ =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | p.2 ≠ 0} := by
    have he : R.supportLine.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.2 ≠ 0} := by
      ext x
      exact (not_congr (hAngleCoordinate_first_support R S hne x)).symm
    rw [he,image_preimage_eq_inter_range,inter_comm,hAngleCoordinate_range]
  rw [hAngleSide_eq_component R S hne S.directionPoint_mem]
  change F '' connectedComponentIn R.supportLine.carrierᶜ S.directionPoint = _
  rw [embedding_image_connectedComponentIn hF
    (R.punctured_subset_compl_support S hne S.directionPoint_mem),hcomp]
  apply connectedComponentIn_positive_linear_cut (hAngleCoordinateDomain_convex R S hne)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  refine ⟨?_,?_⟩
  · rw [← hAngleCoordinate_range]
    exact mem_range_self S.directionPoint
  · change 0 < (hAngleCoordinate R S hne S.directionPoint).2
    rw [hAngleCoordinate_second_point]
    exact zero_lt_one

theorem hAngleCoordinate_image_secondSide {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' hAngleSide S R =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | 0 < p.1} := by
  let F := hAngleCoordinate R S hne
  have hF := (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding
  have hcomp : F '' S.supportLine.carrierᶜ =
      hAngleCoordinateDomain R S hne ∩ {p : ℝ × ℝ | p.1 ≠ 0} := by
    have he : S.supportLine.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.1 ≠ 0} := by
      ext x
      exact (not_congr (hAngleCoordinate_second_support R S hne x)).symm
    rw [he,image_preimage_eq_inter_range,inter_comm,hAngleCoordinate_range]
  rw [hAngleSide_eq_component S R (Ne.symm hne) R.directionPoint_mem]
  change F '' connectedComponentIn S.supportLine.carrierᶜ R.directionPoint = _
  rw [embedding_image_connectedComponentIn hF
    (S.punctured_subset_compl_support R (Ne.symm hne) R.directionPoint_mem),hcomp]
  apply connectedComponentIn_positive_linear_cut (hAngleCoordinateDomain_convex R S hne)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  refine ⟨?_,?_⟩
  · rw [← hAngleCoordinate_range]
    exact mem_range_self R.directionPoint
  · change 0 < (hAngleCoordinate R S hne R.directionPoint).1
    rw [hAngleCoordinate_first_point]
    exact zero_lt_one

theorem hAngleCoordinate_image_interior {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' properHAngleInterior R S =
      hAngleCoordinateDomain R S hne ∩ positiveCoordinateQuadrant := by
  rw [properHAngleInterior,image_inter (hAngleCoordinate_isOpenEmbedding R S hne).injective,
    hAngleCoordinate_image_firstSide,hAngleCoordinate_image_secondSide]
  ext p
  change ((p ∈ hAngleCoordinateDomain R S hne ∧ 0 < p.2) ∧
    p ∈ hAngleCoordinateDomain R S hne ∧ 0 < p.1) ↔
      p ∈ hAngleCoordinateDomain R S hne ∧ 0 < p.1 ∧ 0 < p.2
  tauto

/-- The actual proper exterior, pending no component convention, is this genuine complement set. -/
def properHAngleExterior {z : ℍ} (R S : HRayAt z) : Set ℍ :=
  (R.val ∪ S.val)ᶜ \ properHAngleInterior R S

theorem hAngleCoordinate_image_exterior {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' properHAngleExterior R S =
      hAngleCoordinateDomain R S hne ∩ exteriorCoordinateQuadrant := by
  have hi := (hAngleCoordinate_isOpenEmbedding R S hne).injective
  rw [properHAngleExterior,image_sdiff hi,image_compl_eq_range_sdiff_image hi,
    hAngleCoordinate_range,hAngleCoordinate_image_rayUnion,hAngleCoordinate_image_interior]
  ext p
  simp only [mem_sdiff,mem_inter_iff,positiveCoordinateAxes,positiveCoordinateQuadrant,
    exteriorCoordinateQuadrant,mem_ofPred]
  grind

theorem hAngleCoordinate_image_rayComplement {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleCoordinate R S hne '' (R.val ∪ S.val)ᶜ =
      hAngleCoordinateDomain R S hne \ positiveCoordinateAxes := by
  rw [image_compl_eq_range_sdiff_image (hAngleCoordinate_isOpenEmbedding R S hne).injective,
    hAngleCoordinate_range,hAngleCoordinate_image_rayUnion]
  ext p
  simp only [mem_sdiff,mem_inter_iff]
  tauto

theorem properHAngleInterior_nonempty {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : (properHAngleInterior R S).Nonempty := by
  have him : (hAngleCoordinate R S hne '' properHAngleInterior R S).Nonempty := by
    rw [hAngleCoordinate_image_interior]
    exact coordinateInterior_nonempty (hAngleCoordinateDomain_isOpen R S hne)
      (hAngleCoordinateDomain_zero_mem R S hne)
  exact image_nonempty.mp him

theorem properHAngleExterior_nonempty {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : (properHAngleExterior R S).Nonempty := by
  have him : (hAngleCoordinate R S hne '' properHAngleExterior R S).Nonempty := by
    rw [hAngleCoordinate_image_exterior]
    exact coordinateExterior_nonempty (hAngleCoordinateDomain_isOpen R S hne)
      (hAngleCoordinateDomain_zero_mem R S hne)
  exact image_nonempty.mp him

theorem properHAngleExterior_isPreconnected {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsPreconnected (properHAngleExterior R S) := by
  apply (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding.isInducing.isPreconnected_image.mp
  rw [hAngleCoordinate_image_exterior]
  exact coordinateExterior_isPreconnected (hAngleCoordinateDomain_isOpen R S hne)
    (hAngleCoordinateDomain_convex R S hne) (hAngleCoordinateDomain_zero_mem R S hne)

theorem properHAngleExterior_isOpen {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : IsOpen (properHAngleExterior R S) := by
  apply (hAngleCoordinate_isOpenEmbedding R S hne).isOpen_iff_image_isOpen.mpr
  rw [hAngleCoordinate_image_exterior]
  exact (hAngleCoordinateDomain_isOpen R S hne).inter exteriorCoordinateQuadrant_isOpen

/-- The actual source interior is precisely one genuine component of the complement of its rays. -/
theorem connectedComponentIn_properHAngleInterior {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : ℍ} (hx : x ∈ properHAngleInterior R S) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properHAngleInterior R S := by
  have hF := (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding
  apply hF.injective.image_injective
  rw [embedding_image_connectedComponentIn hF (properHAngleInterior_subset_compl_union R S hx),
    hAngleCoordinate_image_rayComplement,hAngleCoordinate_image_interior]
  apply connectedComponentIn_coordinateInterior (hAngleCoordinateDomain_convex R S hne)
  rw [← hAngleCoordinate_image_interior]
  exact mem_image_of_mem _ hx

/-- The actual source exterior is the second genuine component. -/
theorem connectedComponentIn_properHAngleExterior {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : ℍ} (hx : x ∈ properHAngleExterior R S) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properHAngleExterior R S := by
  have hF := (hAngleCoordinate_isOpenEmbedding R S hne).isEmbedding
  apply hF.injective.image_injective
  rw [embedding_image_connectedComponentIn hF hx.1,hAngleCoordinate_image_rayComplement,
    hAngleCoordinate_image_exterior]
  apply connectedComponentIn_coordinateExterior (hAngleCoordinateDomain_isOpen R S hne)
    (hAngleCoordinateDomain_convex R S hne) (hAngleCoordinateDomain_zero_mem R S hne)
  rw [← hAngleCoordinate_image_exterior]
  exact mem_image_of_mem _ hx

theorem properHAngle_interior_exterior_partition {z : ℍ} (R S : HRayAt z) :
    (R.val ∪ S.val)ᶜ = properHAngleInterior R S ∪ properHAngleExterior R S := by
  ext x
  have hs := properHAngleInterior_subset_compl_union R S
  change x ∉ R.val ∪ S.val ↔ x ∈ properHAngleInterior R S ∨
    (x ∉ R.val ∪ S.val ∧ x ∉ properHAngleInterior R S)
  constructor
  · intro hx
    by_cases hxI : x ∈ properHAngleInterior R S
    · exact Or.inl hxI
    · exact Or.inr ⟨hx,hxI⟩
  · rintro (hxI | hxE)
    · change x ∈ (R.val ∪ S.val)ᶜ
      exact hs hxI
    · exact hxE.1

theorem properHAngle_interior_exterior_disjoint {z : ℍ} (R S : HRayAt z) :
    Disjoint (properHAngleInterior R S) (properHAngleExterior R S) := by
  rw [disjoint_left]
  exact fun _ hx hy => hy.2 hx

/-- These two actual components exhaust all points of the genuine complement. -/
theorem properHAngle_component_classification {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {x : ℍ} (hx : x ∈ (R.val ∪ S.val)ᶜ) :
    connectedComponentIn (R.val ∪ S.val)ᶜ x = properHAngleInterior R S ∨
      connectedComponentIn (R.val ∪ S.val)ᶜ x = properHAngleExterior R S := by
  by_cases hxI : x ∈ properHAngleInterior R S
  · exact Or.inl (connectedComponentIn_properHAngleInterior R S hne hxI)
  · exact Or.inr (connectedComponentIn_properHAngleExterior R S hne ⟨hx,hxI⟩)

/-- Genuine hyperbolic segment convexity becomes actual convexity in the computed
ray coordinates; this is a proved consequence of the actual Klein segment bridge. -/
theorem HConvex.hAngleCoordinate_image {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) {A : Set ℍ} (hA : HConvex A) :
    Convex ℝ (hAngleCoordinate R S hne '' A) := by
  have hk : Convex ℝ (halfPlaneKleinCoordinate '' A) := by
    have hd := (hConvex_iff_cayley_discHConvex A).mp hA
    have hc := (discHConvex_iff_klein_convex (halfPlaneToDisc '' A)).mp hd
    rw [image_image] at hc
    exact hc
  have he : hAngleCoordinate R S hne '' A = hAngleCoordinateLinear R S hne ''
      ((fun x : ℂ => -halfPlaneKleinCoordinate z + x) '' (halfPlaneKleinCoordinate '' A)) := by
    rw [image_image,image_image]
    apply Set.image_congr
    intro x _
    change hAngleCoordinateLinear R S hne (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate z) =
      hAngleCoordinateLinear R S hne (-halfPlaneKleinCoordinate z + halfPlaneKleinCoordinate x)
    congr 1
    abel
  rw [he]
  exact (hk.translate (-halfPlaneKleinCoordinate z)).linear_image
    (hAngleCoordinateLinear R S hne).toLinearMap

/-- The source exterior is not hyperbolically convex: actual coordinate-domain
witnesses force an actual hyperbolic segment to leave it. -/
theorem properHAngleExterior_not_hConvex {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : ¬ HConvex (properHAngleExterior R S) := by
  intro hc
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.hAngleCoordinate_image R S hne hc
  rw [hAngleCoordinate_image_exterior] at he
  exact coordinateExterior_not_convex (hAngleCoordinateDomain_isOpen R S hne)
    (hAngleCoordinateDomain_zero_mem R S hne) he

end
end LowDimensionalTopology.Geometry.Hyperbolic
