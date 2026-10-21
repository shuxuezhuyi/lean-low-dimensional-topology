/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.Finite

/-!
# Actual vertex-based Klein triangle coordinates
-/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem HTriangle.klein_vertices_linearIndependent (T : HTriangle) :
    LinearIndependent ℝ ![halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a,
      halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a] := by
  apply linearIndependent_fin2.mpr
  refine ⟨sub_ne_zero.mpr (halfPlaneKleinCoordinate_injective.ne T.c_ne_a),?_⟩
  intro r he
  change r • (halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a) =
    halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a at he
  obtain ⟨a,t,_,hL⟩ := T.sideLineB.klein_affine_equation
  have ha := (hL T.a).mp (T.rayCA.subset_support T.a_mem_rayCA)
  have hc := (hL T.c).mp T.rayCA.start_mem_support
  have hb : inner ℝ a (halfPlaneKleinCoordinate T.b) = t := by
    have hd : inner ℝ a (halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a) = 0 := by
      rw [← he,inner_smul_right,inner_sub_right,hc,ha,sub_self,mul_zero]
    rw [inner_sub_right,ha] at hd
    linarith
  exact T.b_not_mem_sideLineB ((hL T.b).mpr hb)

def HTriangle.kleinBasis (T : HTriangle) : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank T.klein_vertices_linearIndependent
    (by simp only [Fintype.card_fin,Complex.finrank_real_complex])

theorem HTriangle.kleinBasis_zero (T : HTriangle) :
    T.kleinBasis 0 = halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 0 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem HTriangle.kleinBasis_one (T : HTriangle) :
    T.kleinBasis 1 = halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 1 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

def HTriangle.coordinateLinear (T : HTriangle) : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  T.kleinBasis.equivFun.trans (LinearEquiv.finTwoArrow ℝ ℝ)

def HTriangle.coordinateHomeomorph (T : HTriangle) : ℂ ≃ₜ ℝ × ℝ :=
  (Homeomorph.subRight (halfPlaneKleinCoordinate T.a)).trans
    T.coordinateLinear.toContinuousLinearEquiv.toHomeomorph

def HTriangle.coordinate (T : HTriangle) (x : ℍ) : ℝ × ℝ :=
  T.coordinateHomeomorph (halfPlaneKleinCoordinate x)

def HTriangle.coordinateDomain (T : HTriangle) : Set (ℝ × ℝ) :=
  T.coordinateHomeomorph '' Metric.ball (0 : ℂ) 1

theorem HTriangle.coordinate_a (T : HTriangle) : T.coordinate T.a = (0,0) := by
  change T.coordinateLinear (halfPlaneKleinCoordinate T.a - halfPlaneKleinCoordinate T.a) = 0
  rw [sub_self,map_zero]

theorem HTriangle.coordinate_b (T : HTriangle) : T.coordinate T.b = (1,0) := by
  change T.coordinateLinear (halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a) = _
  rw [← T.kleinBasis_zero]
  change (T.kleinBasis.equivFun (T.kleinBasis 0) 0,
    T.kleinBasis.equivFun (T.kleinBasis 0) 1) = (1,0)
  simp only [Basis.equivFun_self,ite_true,Fin.zero_ne_one,ite_false]

theorem HTriangle.coordinate_c (T : HTriangle) : T.coordinate T.c = (0,1) := by
  change T.coordinateLinear (halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a) = _
  rw [← T.kleinBasis_one]
  change (T.kleinBasis.equivFun (T.kleinBasis 1) 0,
    T.kleinBasis.equivFun (T.kleinBasis 1) 1) = (0,1)
  simp only [Basis.equivFun_self,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true]

theorem HTriangle.coordinate_isOpenEmbedding (T : HTriangle) :
    Topology.IsOpenEmbedding T.coordinate :=
  T.coordinateHomeomorph.isOpenEmbedding.comp isOpenEmbedding_halfPlaneKleinCoordinate

theorem HTriangle.coordinate_range (T : HTriangle) : range T.coordinate = T.coordinateDomain := by
  change range (T.coordinateHomeomorph ∘ halfPlaneKleinCoordinate) = _
  rw [range_comp,range_halfPlaneKleinCoordinate]
  rfl

theorem HTriangle.coordinateDomain_isOpen (T : HTriangle) : IsOpen T.coordinateDomain :=
  T.coordinateHomeomorph.isOpenMap _ Metric.isOpen_ball

theorem HTriangle.coordinateDomain_convex (T : HTriangle) : Convex ℝ T.coordinateDomain := by
  have he : T.coordinateDomain = T.coordinateLinear ''
      ((fun x : ℂ => -halfPlaneKleinCoordinate T.a + x) '' Metric.ball (0 : ℂ) 1) := by
    rw [image_image]
    apply image_congr
    intro x _
    change T.coordinateLinear (x - halfPlaneKleinCoordinate T.a) =
      T.coordinateLinear (-halfPlaneKleinCoordinate T.a + x)
    congr 1
    abel
  rw [he]
  exact ((convex_ball (0 : ℂ) 1).translate (-halfPlaneKleinCoordinate T.a)).linear_image
    T.coordinateLinear.toLinearMap

theorem HTriangle.klein_reconstruction (T : HTriangle) (x : ℍ) :
    halfPlaneKleinCoordinate x = halfPlaneKleinCoordinate T.a +
      (T.coordinate x).1 • (halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a) +
      (T.coordinate x).2 • (halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a) := by
  have he := T.kleinBasis.sum_repr (halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate T.a)
  rw [Fin.sum_univ_two,T.kleinBasis_zero,T.kleinBasis_one] at he
  change (T.coordinate x).1 • (halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a) +
    (T.coordinate x).2 • (halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a) =
      halfPlaneKleinCoordinate x - halfPlaneKleinCoordinate T.a at he
  calc
    _ = (T.coordinate x).1 • (halfPlaneKleinCoordinate T.b - halfPlaneKleinCoordinate T.a) +
      (T.coordinate x).2 • (halfPlaneKleinCoordinate T.c - halfPlaneKleinCoordinate T.a) +
        halfPlaneKleinCoordinate T.a := sub_eq_iff_eq_add.mp he.symm
    _ = _ := by abel


theorem HTriangle.inner_klein_reconstruction (T : HTriangle) (n : ℂ) (x : ℍ) :
    inner ℝ n (halfPlaneKleinCoordinate x) = inner ℝ n (halfPlaneKleinCoordinate T.a) +
      (T.coordinate x).1 * (inner ℝ n (halfPlaneKleinCoordinate T.b) - inner ℝ n (halfPlaneKleinCoordinate T.a)) +
      (T.coordinate x).2 * (inner ℝ n (halfPlaneKleinCoordinate T.c) - inner ℝ n (halfPlaneKleinCoordinate T.a)) := by
  conv_lhs => rw [T.klein_reconstruction x]
  simp only [inner_add_right,inner_smul_right,inner_sub_right]

theorem HTriangle.sideLineC_iff_coordinate (T : HTriangle) (x : ℍ) :
    x ∈ T.sideLineC.carrier ↔ (T.coordinate x).2 = 0 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineC.klein_affine_equation
  have ha := (hL T.a).mp T.rayAB.start_mem_support
  have hb := (hL T.b).mp (T.rayAB.subset_support T.b_mem_rayAB)
  have hc : inner ℝ n (halfPlaneKleinCoordinate T.c) ≠ t :=
    fun he => T.c_not_mem_sideLineC ((hL T.c).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [ha,hb] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : (T.coordinate x).2 * (inner ℝ n (halfPlaneKleinCoordinate T.c) - t) = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hc)
  · intro hx
    rw [hx] at he
    nlinarith

theorem HTriangle.sideLineB_iff_coordinate (T : HTriangle) (x : ℍ) :
    x ∈ T.sideLineB.carrier ↔ (T.coordinate x).1 = 0 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineB.klein_affine_equation
  have ha := (hL T.a).mp (T.rayCA.subset_support T.a_mem_rayCA)
  have hc := (hL T.c).mp T.rayCA.start_mem_support
  have hb : inner ℝ n (halfPlaneKleinCoordinate T.b) ≠ t :=
    fun he => T.b_not_mem_sideLineB ((hL T.b).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [ha,hc] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : (T.coordinate x).1 * (inner ℝ n (halfPlaneKleinCoordinate T.b) - t) = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hb)
  · intro hx
    rw [hx] at he
    nlinarith

theorem HTriangle.sideLineA_iff_coordinate (T : HTriangle) (x : ℍ) :
    x ∈ T.sideLineA.carrier ↔ (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineA.klein_affine_equation
  have hb := (hL T.b).mp T.rayBC.start_mem_support
  have hc := (hL T.c).mp (T.rayBC.subset_support T.c_mem_rayBC)
  have ha : inner ℝ n (halfPlaneKleinCoordinate T.a) ≠ t :=
    fun he => T.a_not_mem_sideLineA ((hL T.a).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [hb,hc] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : ((T.coordinate x).1 + (T.coordinate x).2 - 1) *
        (t - inner ℝ n (halfPlaneKleinCoordinate T.a)) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr ha.symm))
  · intro hx
    have hm : (T.coordinate x).1 * (t - inner ℝ n (halfPlaneKleinCoordinate T.a)) +
        (T.coordinate x).2 * (t - inner ℝ n (halfPlaneKleinCoordinate T.a)) =
          t - inner ℝ n (halfPlaneKleinCoordinate T.a) := by
      rw [← add_mul,hx,one_mul]
    linarith


/-- In a convex domain, a nonzero continuous scalar cut has the expected positive component
whenever that positive side is convex. -/
theorem connectedComponentIn_positive_convex_cut {D : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (hpos : Convex ℝ (D ∩ {p | 0 < f p}))
    {x : ℝ × ℝ} (hx : x ∈ D ∩ {p | 0 < f p}) :
    connectedComponentIn (D ∩ {p | f p ≠ 0}) x = D ∩ {p | 0 < f p} := by
  have hsub : D ∩ {p | 0 < f p} ⊆ D ∩ {p | f p ≠ 0} := fun _ hy => ⟨hy.1,ne_of_gt hy.2⟩
  apply subset_antisymm
  · intro y hy
    have hyA := connectedComponentIn_subset _ _ hy
    refine ⟨hyA.1,?_⟩
    change 0 < f y
    by_contra! hle
    have hC := (isPreconnected_connectedComponentIn
      (F := D ∩ {p | f p ≠ 0}) (x := x)).image f hf.continuousOn
    have hxC := mem_connectedComponentIn (hsub hx)
    obtain ⟨v,hv,hv0⟩ := hC.ordConnected.out (mem_image_of_mem f hy)
      (mem_image_of_mem f hxC) (show (0 : ℝ) ∈ Icc (f y) (f x) from ⟨hle,hx.2.le⟩)
    exact (connectedComponentIn_subset _ _ hv).2 hv0
  · exact hpos.isPreconnected.subset_connectedComponentIn hx hsub

theorem HTriangle.coordinate_image_halfPlaneA (T : HTriangle) :
    T.coordinate '' T.halfPlaneA = T.coordinateDomain ∩ {p : ℝ × ℝ | p.1 + p.2 < 1} := by
  let F := T.coordinate
  have hF := T.coordinate_isOpenEmbedding.isEmbedding
  have hcut : F '' T.sideLineA.carrierᶜ =
      T.coordinateDomain ∩ {p : ℝ × ℝ | 1 - p.1 - p.2 ≠ 0} := by
    have he : T.sideLineA.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | 1 - p.1 - p.2 ≠ 0} := by
      ext x
      change x ∉ T.sideLineA.carrier ↔ 1 - (F x).1 - (F x).2 ≠ 0
      rw [T.sideLineA_iff_coordinate]
      constructor <;> intro h hn <;> apply h <;> linarith
    rw [he,image_preimage_eq_inter_range,inter_comm,T.coordinate_range]
  change F '' connectedComponentIn T.sideLineA.carrierᶜ T.a = _
  rw [embedding_image_connectedComponentIn hF T.a_not_mem_sideLineA,hcut]
  have hc : Convex ℝ {p : ℝ × ℝ | 0 < 1 - p.1 - p.2} := by
    have he : {p : ℝ × ℝ | 0 < 1 - p.1 - p.2} = {p | p.1 + p.2 < 1} := by
      ext p
      change (0 < 1 - p.1 - p.2) ↔ p.1 + p.2 < 1
      constructor <;> intro h <;> linarith
    rw [he]
    exact convex_halfSpace_lt
      ((ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear) (1 : ℝ)
  rw [connectedComponentIn_positive_convex_cut (fun p : ℝ × ℝ => 1 - p.1 - p.2)
    ((continuous_const.sub continuous_fst).sub continuous_snd)
    (T.coordinateDomain_convex.inter hc)]
  · ext p
    simp only [mem_inter_iff,mem_ofPred]
    constructor <;> rintro ⟨hp,hs⟩ <;> refine ⟨hp,?_⟩ <;> linarith
  · refine ⟨?_,?_⟩
    · rw [← T.coordinate_range]
      exact mem_range_self T.a
    · change 0 < 1 - (T.coordinate T.a).1 - (T.coordinate T.a).2
      rw [T.coordinate_a]
      norm_num

theorem HTriangle.coordinate_image_halfPlaneB (T : HTriangle) :
    T.coordinate '' T.halfPlaneB = T.coordinateDomain ∩ {p : ℝ × ℝ | 0 < p.1} := by
  let F := T.coordinate
  have hF := T.coordinate_isOpenEmbedding.isEmbedding
  have hcut : F '' T.sideLineB.carrierᶜ = T.coordinateDomain ∩ {p : ℝ × ℝ | p.1 ≠ 0} := by
    have he : T.sideLineB.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.1 ≠ 0} := by
      ext x
      exact not_congr (T.sideLineB_iff_coordinate x)
    rw [he,image_preimage_eq_inter_range,inter_comm,T.coordinate_range]
  change F '' connectedComponentIn T.sideLineB.carrierᶜ T.b = _
  rw [embedding_image_connectedComponentIn hF T.b_not_mem_sideLineB,hcut]
  apply connectedComponentIn_positive_linear_cut T.coordinateDomain_convex
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  refine ⟨?_,?_⟩
  · rw [← T.coordinate_range]
    exact mem_range_self T.b
  · change 0 < (T.coordinate T.b).1
    rw [T.coordinate_b]
    exact zero_lt_one

theorem HTriangle.coordinate_image_halfPlaneC (T : HTriangle) :
    T.coordinate '' T.halfPlaneC = T.coordinateDomain ∩ {p : ℝ × ℝ | 0 < p.2} := by
  let F := T.coordinate
  have hF := T.coordinate_isOpenEmbedding.isEmbedding
  have hcut : F '' T.sideLineC.carrierᶜ = T.coordinateDomain ∩ {p : ℝ × ℝ | p.2 ≠ 0} := by
    have he : T.sideLineC.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.2 ≠ 0} := by
      ext x
      exact not_congr (T.sideLineC_iff_coordinate x)
    rw [he,image_preimage_eq_inter_range,inter_comm,T.coordinate_range]
  change F '' connectedComponentIn T.sideLineC.carrierᶜ T.c = _
  rw [embedding_image_connectedComponentIn hF T.c_not_mem_sideLineC,hcut]
  apply connectedComponentIn_positive_linear_cut T.coordinateDomain_convex
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  refine ⟨?_,?_⟩
  · rw [← T.coordinate_range]
    exact mem_range_self T.c
  · change 0 < (T.coordinate T.c).2
    rw [T.coordinate_c]
    exact zero_lt_one

def standardOpenTriangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

def standardClosedTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem HTriangle.coordinate_image_interior_cut (T : HTriangle) :
    T.coordinate '' T.interior = T.coordinateDomain ∩ standardOpenTriangle := by
  rw [T.interior_eq_halfPlanes,
    image_inter T.coordinate_isOpenEmbedding.injective,
    image_inter T.coordinate_isOpenEmbedding.injective,
    T.coordinate_image_halfPlaneA,T.coordinate_image_halfPlaneB,T.coordinate_image_halfPlaneC]
  ext p
  simp only [mem_inter_iff,standardOpenTriangle,mem_ofPred]
  tauto


theorem standardClosedTriangle_subset_convex {D : Set (ℝ × ℝ)} (hD : Convex ℝ D)
    (h0 : (0,0) ∈ D) (h1 : (1,0) ∈ D) (h2 : (0,1) ∈ D) : standardClosedTriangle ⊆ D := by
  intro p hp
  change 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 at hp
  have hm := hD.sum_mem (t := Finset.univ)
    (w := ![1 - p.1 - p.2,p.1,p.2]) (z := ![(0,0),(1,0),(0,1)])
    (by
      intro i _
      fin_cases i
      · change 0 ≤ 1 - p.1 - p.2
        linarith
      · exact hp.1
      · exact hp.2.1)
    (by simp [Fin.sum_univ_three]; ring)
    (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_three,smul_eq_mul] using hm

theorem HTriangle.standardClosedTriangle_subset_domain (T : HTriangle) :
    standardClosedTriangle ⊆ T.coordinateDomain := by
  apply standardClosedTriangle_subset_convex T.coordinateDomain_convex
  · rw [← T.coordinate_range,← T.coordinate_a]
    exact mem_range_self T.a
  · rw [← T.coordinate_range,← T.coordinate_b]
    exact mem_range_self T.b
  · rw [← T.coordinate_range,← T.coordinate_c]
    exact mem_range_self T.c

theorem HTriangle.coordinate_image_interior (T : HTriangle) :
    T.coordinate '' T.interior = standardOpenTriangle := by
  rw [T.coordinate_image_interior_cut]
  apply inter_eq_right.mpr
  intro p hp
  apply T.standardClosedTriangle_subset_domain
  exact ⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩

theorem HTriangle.interior_nonempty (T : HTriangle) : T.interior.Nonempty := by
  have he : (T.coordinate '' T.interior).Nonempty := by
    rw [T.coordinate_image_interior]
    exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩
  exact image_nonempty.mp he

theorem DiscTriangle.interior_nonempty (T : DiscTriangle) : T.interior.Nonempty := by
  rw [T.interior_eq_cayley]
  exact T.toHalfPlane.interior_nonempty.image _

/-- The coordinate map is the restriction of an actual real affine equivalence. -/
def HTriangle.coordinateAffine (T : HTriangle) : ℂ →ᵃ[ℝ] ℝ × ℝ :=
  T.coordinateLinear.toAffineEquiv.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ (halfPlaneKleinCoordinate T.a)).symm.toAffineMap

theorem HTriangle.coordinateAffine_apply (T : HTriangle) (x : ℂ) :
    T.coordinateAffine x = T.coordinateHomeomorph x := rfl

theorem halfPlaneKlein_image_closedHSegment (z w : ℍ) :
    halfPlaneKleinCoordinate '' closedHSegment z w =
      segment ℝ (halfPlaneKleinCoordinate z) (halfPlaneKleinCoordinate w) := by
  have he : halfPlaneToDisc '' closedHSegment z w =
      closedDiscHSegment (halfPlaneToDisc z) (halfPlaneToDisc w) := by
    rw [closedDiscHSegment_eq_cayley_image,
      discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc]
  calc
    _ = kleinCoordinate '' (halfPlaneToDisc '' closedHSegment z w) := (image_image _ _ _).symm
    _ = _ := by rw [he,klein_image_closedDiscHSegment]; rfl

theorem HTriangle.coordinate_image_closedHSegment (T : HTriangle) (z w : ℍ) :
    T.coordinate '' closedHSegment z w = segment ℝ (T.coordinate z) (T.coordinate w) := by
  calc
    _ = T.coordinateAffine '' (halfPlaneKleinCoordinate '' closedHSegment z w) :=
      (image_image _ _ _).symm
    _ = _ := by
      rw [halfPlaneKlein_image_closedHSegment]
      exact image_segment ℝ T.coordinateAffine (halfPlaneKleinCoordinate z) (halfPlaneKleinCoordinate w)


theorem HRayAt.hConvex {z : ℍ} (R : HRayAt z) : HConvex R.val := by
  obtain ⟨γ,hγ,s,_,hor,_⟩ := R.isRay
  rcases hor with hR | hR
  · rw [hR]
    apply (hConvex_iff_convex_parameter hγ (image_subset_range _ _)).mpr
    rw [preimage_image_eq _ hγ.1.injective]
    exact convex_Ici s
  · rw [hR]
    apply (hConvex_iff_convex_parameter hγ (image_subset_range _ _)).mpr
    rw [preimage_image_eq _ hγ.1.injective]
    exact convex_Iic s

theorem HTriangle.mem_closedHSegment_iff_coordinate (T : HTriangle) (z w x : ℍ) :
    x ∈ closedHSegment z w ↔ T.coordinate x ∈ segment ℝ (T.coordinate z) (T.coordinate w) := by
  rw [← T.coordinate_image_closedHSegment]
  exact T.coordinate_isOpenEmbedding.injective.mem_set_image.symm

theorem standard_opposite_segment :
    segment ℝ ((1,0) : ℝ × ℝ) (0,1) =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} := by
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hab,hp⟩
    have he : p = (a,b) := by
      rw [← hp]
      ext <;> simp
    rw [he]
    exact ⟨ha,hb,hab⟩
  · intro hp
    refine ⟨p.1,p.2,hp.1,hp.2.1,hp.2.2,?_⟩
    ext <;> simp

theorem HTriangle.mem_sideA_iff_coordinate (T : HTriangle) (x : ℍ) :
    x ∈ T.sideA ↔ 0 ≤ (T.coordinate x).1 ∧ 0 ≤ (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  change x ∈ closedHSegment T.b T.c ↔ _
  rw [T.mem_closedHSegment_iff_coordinate,T.coordinate_b,T.coordinate_c,standard_opposite_segment]
  rfl

theorem HTriangle.mem_open_sideA_iff_coordinate (T : HTriangle) (x : ℍ) :
    x ∈ openHSegment T.b T.c ↔ 0 < (T.coordinate x).1 ∧ 0 < (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  rw [mem_openHSegment_iff T.b_ne_c]
  change (x ∈ T.sideA ∧ x ≠ T.b ∧ x ≠ T.c) ↔ _
  rw [T.mem_sideA_iff_coordinate]
  constructor
  · rintro ⟨⟨hu,hv,hs⟩,hxb,hxc⟩
    have hu0 : (T.coordinate x).1 ≠ 0 := by
      intro he
      apply hxc
      apply T.coordinate_isOpenEmbedding.injective
      rw [T.coordinate_c]
      ext <;> dsimp <;> linarith
    have hv0 : (T.coordinate x).2 ≠ 0 := by
      intro he
      apply hxb
      apply T.coordinate_isOpenEmbedding.injective
      rw [T.coordinate_b]
      ext <;> dsimp <;> linarith
    exact ⟨lt_of_le_of_ne hu (Ne.symm hu0),lt_of_le_of_ne hv (Ne.symm hv0),hs⟩
  · rintro ⟨hu,hv,hs⟩
    refine ⟨⟨hu.le,hv.le,hs⟩,?_,?_⟩
    · intro he
      rw [he,T.coordinate_b] at hv
      exact lt_irrefl 0 hv
    · intro he
      rw [he,T.coordinate_c] at hu
      exact lt_irrefl 0 hu

theorem HTriangle.interior_coordinate (T : HTriangle) {x : ℍ} (hx : x ∈ T.interior) :
    0 < (T.coordinate x).1 ∧ 0 < (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 < 1 := by
  have he := mem_image_of_mem T.coordinate hx
  rw [T.coordinate_image_interior] at he
  exact he

theorem HTriangle.a_ne_of_mem_interior (T : HTriangle) {x : ℍ} (hx : x ∈ T.interior) : T.a ≠ x := by
  intro he
  have hc := (T.interior_coordinate hx).1
  rw [← he,T.coordinate_a] at hc
  exact lt_irrefl 0 hc

theorem HTriangle.ray_meets_opposite_side (T : HTriangle) (R : HRayAt T.a)
    {x : ℍ} (hx : x ∈ T.interior) (hxR : x ∈ R.val) :
    ∃ y : ℍ, y ∈ openHSegment T.b T.c ∧ y ∈ R.val := by
  obtain ⟨hu,hv,hs⟩ := T.interior_coordinate hx
  let s := (T.coordinate x).1 + (T.coordinate x).2
  have hs0 : 0 < s := add_pos hu hv
  let p : ℝ × ℝ := ((T.coordinate x).1 / s,(T.coordinate x).2 / s)
  have hp1 : 0 < p.1 := div_pos hu hs0
  have hp2 : 0 < p.2 := div_pos hv hs0
  have hpsum : p.1 + p.2 = 1 := by
    change (T.coordinate x).1 / s + (T.coordinate x).2 / s = 1
    rw [← add_div]
    exact div_self (ne_of_gt hs0)
  have hpD : p ∈ T.coordinateDomain :=
    T.standardClosedTriangle_subset_domain ⟨hp1.le,hp2.le,hpsum.le⟩
  rw [← T.coordinate_range] at hpD
  obtain ⟨y,hy⟩ := hpD
  have hySide : y ∈ openHSegment T.b T.c := by
    rw [T.mem_open_sideA_iff_coordinate,hy]
    exact ⟨hp1,hp2,hpsum⟩
  have hay : T.a ≠ y := by
    intro he
    have hh : (T.coordinate T.a).1 = p.1 := by rw [he,hy]
    rw [T.coordinate_a] at hh
    exact (ne_of_gt hp1) hh.symm
  have hxSeg : x ∈ closedHSegment T.a y := by
    rw [T.mem_closedHSegment_iff_coordinate,T.coordinate_a,hy]
    refine ⟨1-s,s,by linarith,hs0.le,by ring,?_⟩
    ext <;> simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      smul_eq_mul,mul_zero,zero_add]
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
  let S := hRayThrough T.a y hay
  have hyS : y ∈ S.val := hRayThrough_mem _ _ _
  have hxS : x ∈ S.val := S.hConvex _ S.start_mem _ hyS hxSeg
  have hRS : R = S := R.eq_of_shared_point S (T.a_ne_of_mem_interior hx) hxR hxS
  exact ⟨y,hySide,hRS.symm ▸ hyS⟩


theorem HTriangle.open_sideA_subset_angleInteriorA (T : HTriangle) :
    openHSegment T.b T.c ⊆ T.angleInteriorA := by
  intro x hx
  obtain ⟨hu,hv,_⟩ := (T.mem_open_sideA_iff_coordinate x).mp hx
  have hxD : T.coordinate x ∈ T.coordinateDomain := by
    rw [← T.coordinate_range]
    exact mem_range_self x
  rw [T.angleInteriorA_eq_halfPlanes]
  constructor
  · apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
    rw [T.coordinate_image_halfPlaneB]
    exact ⟨hxD,hu⟩
  · apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
    rw [T.coordinate_image_halfPlaneC]
    exact ⟨hxD,hv⟩

theorem DiscTriangle.ray_meets_opposite_side (T : DiscTriangle) (R : DiscRayAt T.a)
    {x : 𝔻} (hx : x ∈ T.interior) (hxR : x ∈ R.val) :
    ∃ y : 𝔻, y ∈ openDiscHSegment T.b T.c ∧ y ∈ R.val := by
  have hxH : discToHalfPlane x ∈ T.toHalfPlane.interior := by
    rw [T.interior_eq_cayley] at hx
    obtain ⟨u,hu,he⟩ := hx
    have he' := congrArg discToHalfPlane he
    rw [discToHalfPlane_halfPlaneToDisc] at he'
    exact he' ▸ hu
  obtain ⟨y,hy,hyR⟩ := T.toHalfPlane.ray_meets_opposite_side R.toHalfPlane hxH ⟨x,hxR,rfl⟩
  refine ⟨halfPlaneToDisc y,?_,?_⟩
  · rw [openDiscHSegment_eq_cayley_image]
    exact ⟨y,hy,rfl⟩
  · rw [R.carrier_eq_cayley]
    exact ⟨y,hyR,rfl⟩

theorem DiscTriangle.open_sideA_subset_angleInteriorA (T : DiscTriangle) :
    openDiscHSegment T.b T.c ⊆ T.angleInteriorA := by
  rw [openDiscHSegment_eq_cayley_image,T.angleInteriorA_eq_cayley]
  exact image_mono T.toHalfPlane.open_sideA_subset_angleInteriorA

end
end LowDimensionalTopology.Geometry.Hyperbolic
