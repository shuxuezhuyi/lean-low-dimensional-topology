/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleCoordinates
@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Actual components of a side-line complement are determined by the genuine Klein chart. -/
theorem ClosedDiscTriangle.coordinate_image_component_cut (T : ClosedDiscTriangle)
    (L : HalfPlaneLine) (f : (ℝ × ℝ) → ℝ) (hf : Continuous f)
    (hline : ∀ x, x ∈ L.carrier ↔ f (T.halfPlaneCoordinate x) = 0)
    (hconv : Convex ℝ (T.openCoordinateDomain ∩ {p | 0 < f p}))
    (m : ℍ) (hm : 0 < f (T.halfPlaneCoordinate m)) :
    T.halfPlaneCoordinate '' openHHalfPlane L m = T.openCoordinateDomain ∩ {p | 0 < f p} := by
  let F := T.halfPlaneCoordinate
  have hF := T.halfPlaneCoordinate_isOpenEmbedding.isEmbedding
  have hmN : m ∈ L.carrierᶜ := fun h => (ne_of_gt hm) ((hline m).mp h)
  have hcomp : F '' L.carrierᶜ = T.openCoordinateDomain ∩ {p | f p ≠ 0} := by
    have he : L.carrierᶜ = F ⁻¹' {p | f p ≠ 0} := by
      ext x
      exact not_congr (hline x)
    rw [he,image_preimage_eq_inter_range,inter_comm,T.halfPlaneCoordinate_range]
  change F '' connectedComponentIn L.carrierᶜ m = _
  rw [embedding_image_connectedComponentIn hF hmN,hcomp]
  apply connectedComponentIn_positive_convex_cut f hf hconv
  refine ⟨?_,hm⟩
  rw [← T.halfPlaneCoordinate_range]
  exact mem_range_self m

theorem ClosedDiscTriangle.mem_component_iff_cut (T : ClosedDiscTriangle)
    (L : HalfPlaneLine) (f : (ℝ × ℝ) → ℝ) (hf : Continuous f)
    (hline : ∀ x, x ∈ L.carrier ↔ f (T.halfPlaneCoordinate x) = 0)
    (hconv : Convex ℝ (T.openCoordinateDomain ∩ {p | 0 < f p}))
    (m : ℍ) (hm : 0 < f (T.halfPlaneCoordinate m)) (x : ℍ) :
    x ∈ openHHalfPlane L m ↔ 0 < f (T.halfPlaneCoordinate x) := by
  rw [← T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image,
    T.coordinate_image_component_cut L f hf hline hconv m hm]
  exact and_iff_right (by rw [← T.halfPlaneCoordinate_range]; exact mem_range_self x)

/-- The entire genuine finite-or-ideal triangle is the intersection of its three actual half-planes. -/
theorem ClosedDiscTriangle.halfPlaneInterior_eq_components (T : ClosedDiscTriangle)
    (m : ℍ) (hm : m ∈ T.halfPlaneInterior) :
    T.halfPlaneInterior = openHHalfPlane T.sideLineA.toHalfPlane m ∩
      (openHHalfPlane T.sideLineB.toHalfPlane m ∩ openHHalfPlane T.sideLineC.toHalfPlane m) := by
  have hp := (T.mem_halfPlaneInterior_iff m).mp hm
  have hB (x : ℍ) : x ∈ openHHalfPlane T.sideLineB.toHalfPlane m ↔
      0 < (T.halfPlaneCoordinate x).1 :=
    T.mem_component_iff_cut _ Prod.fst continuous_fst
      (fun x => (T.halfPlaneCoordinate_second_line x).symm)
      (T.openCoordinateDomain_convex.inter
        (convex_halfSpace_gt (ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.isLinear (0:ℝ))) m hp.1 x
  have hC (x : ℍ) : x ∈ openHHalfPlane T.sideLineC.toHalfPlane m ↔
      0 < (T.halfPlaneCoordinate x).2 :=
    T.mem_component_iff_cut _ Prod.snd continuous_snd
      (fun x => (T.halfPlaneCoordinate_first_line x).symm)
      (T.openCoordinateDomain_convex.inter
        (convex_halfSpace_gt (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (0:ℝ))) m hp.2.1 x
  have hline : ∀ x, x ∈ T.sideLineA.toHalfPlane.carrier ↔
      1-(T.halfPlaneCoordinate x).1-(T.halfPlaneCoordinate x).2 = 0 := by
    intro x
    rw [← T.halfPlaneCoordinate_opposite_line x]
    constructor <;> intro h <;> linarith only [h]
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 < 1-p.1-p.2} := by
    have he : {p : ℝ × ℝ | 0 < 1-p.1-p.2} = {p | p.1+p.2 < 1} := by
      ext p
      change (0 < 1-p.1-p.2) ↔ p.1+p.2 < 1
      constructor <;> intro h <;> linarith only [h]
    rw [he]
    exact convex_halfSpace_lt
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (1:ℝ)
  have hA (x : ℍ) : x ∈ openHHalfPlane T.sideLineA.toHalfPlane m ↔
      0 < 1-(T.halfPlaneCoordinate x).1-(T.halfPlaneCoordinate x).2 :=
    T.mem_component_iff_cut _ (fun p => 1-p.1-p.2)
      ((continuous_const.sub continuous_fst).sub continuous_snd) hline
      (T.openCoordinateDomain_convex.inter hconv) m (by linarith only [hp.2.2]) x
  ext x
  rw [T.mem_halfPlaneInterior_iff,mem_inter_iff,mem_inter_iff,hA,hB,hC]
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨by linarith only [h3],h1,h2⟩
  · rintro ⟨h3,h1,h2⟩
    exact ⟨h1,h2,by linarith only [h3]⟩

theorem extendedCayley_symm_coe_disc (z : 𝔻) :
    extendedCayley.symm ((z : ℂ) : OnePoint ℂ) = extendedHalfPlanePoint (discToHalfPlane z) := by
  apply extendedCayley.injective
  rw [extendedCayley.apply_symm_apply]
  change ((z : ℂ) : OnePoint ℂ) = extendedCayley (((discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ)
  rw [extendedCayley_halfPlane,halfPlaneToDisc_discToHalfPlane]

theorem ClosedDiscTriangle.closedCarrier_eq_closedModelClosure (T : ClosedDiscTriangle) :
    T.closedCarrier = discClosedModelClosure T.interior := by
  let triangleAreaClosedDiscCompact : CompactSpace 𝕔𝔻 := closedDiscCompactSpace
  have hi : Topology.IsClosedEmbedding ((↑) : 𝕔𝔻 → ℂ) :=
    Complex.UnitClosedDisc.continuous_coe.isClosedEmbedding Complex.UnitClosedDisc.isEmbedding_coe.injective
  apply hi.injective.image_injective
  rw [discClosedModelClosure,← hi.closure_image_eq,image_image]
  change T.complexClosedCarrier = closure (((↑) : 𝔻 → ℂ) '' T.interior)
  rw [T.interior_complex_image,T.complexInterior_closure]

theorem ClosedDiscTriangle.discToHalfPlane_image_interior (T : ClosedDiscTriangle) :
    discToHalfPlane '' T.interior = T.halfPlaneInterior := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change halfPlaneToDisc (discToHalfPlane z) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  · intro hx
    exact ⟨halfPlaneToDisc x,hx,discToHalfPlane_halfPlaneToDisc x⟩

/-- Every genuine ideal point of the closed triangle is an actual ideal accumulation point
of its entire open interior. -/
theorem ClosedDiscTriangle.idealPoint_mem_traceInterior (T : ClosedDiscTriangle)
    (p : 𝕔𝔻) (hp : p ∈ T.closedCarrier) (hideal : ‖(p : ℂ)‖ = 1) :
    extendedCayley.symm (closedDiscToExtended p) ∈ hTraceIdealEndpoints T.halfPlaneInterior := by
  have hdisc : p ∈ discClosedModelClosure T.interior := by
    rwa [← T.closedCarrier_eq_closedModelClosure]
  have he := mem_image_of_mem closedDiscToExtended hdisc
  rw [discClosedModelClosure_ambient] at he
  have hmem := mem_image_of_mem extendedCayley.symm he
  rw [extendedCayley.symm.image_closure,image_image] at hmem
  simp_rw [extendedCayley_symm_coe_disc] at hmem
  rw [← image_image,T.discToHalfPlane_image_interior] at hmem
  refine ⟨hmem,?_⟩
  rw [idealBoundary_cayley_iff,extendedCayley.apply_symm_apply]
  simpa only [closedDiscToExtended,coe_mem_extendedDiscIdealBoundary] using hideal

/-- An actual infinite ideal accumulation point forbids any Euclidean boundedness. -/
theorem hTraceIdealEndpoints_infty_unbounded (S : Set ℍ)
    (hEnd : (∞ : OnePoint ℂ) ∈ hTraceIdealEndpoints S) (c : ℂ) (R : ℝ) :
    ∃ z ∈ S, R < ‖(z : ℂ)-c‖ := by
  by_contra! h
  have hK : IsCompact (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall c R) :=
    (isCompact_closedBall c R).image OnePoint.continuous_coe
  have hsub : extendedHalfPlanePoint '' S ⊆
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall c R := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨(z : ℂ),?_,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm] using h z hz
  obtain ⟨z,_,he⟩ := closure_minimal hsub hK.isClosed hEnd.1
  exact OnePoint.coe_ne_infty z he

/-- Points in the interior-circle component remain strictly inside that circle. -/
theorem openHHalfPlane_circle_inside_subset (c r : ℝ) (hr : 0 < r) (z : ℍ)
    (hz : ‖(z : ℂ)-(c : ℂ)‖ < r) :
    openHHalfPlane (.circle c r hr) z ⊆ {u : ℍ | ‖(u : ℂ)-(c : ℂ)‖ < r} := by
  let L := HalfPlaneLine.circle c r hr
  let f : ℍ → ℝ := fun u => ‖(u : ℂ)-(c : ℂ)‖
  have hc : Continuous f := (UpperHalfPlane.continuous_coe.sub continuous_const).norm
  have hzN : z ∈ L.carrierᶜ := ne_of_lt hz
  intro u hu
  have hp := (isPreconnected_connectedComponentIn (F := L.carrierᶜ) (x := z)).image f hc.continuousOn
  have hzI := mem_image_of_mem f (mem_connectedComponentIn hzN)
  have huI := mem_image_of_mem f hu
  change f u < r
  by_contra! hle
  obtain ⟨v,hv,he⟩ := hp.ordConnected.out hzI huI (show r ∈ Icc (f z) (f u) from ⟨hz.le,hle⟩)
  exact connectedComponentIn_subset L.carrierᶜ z hv he

/-- The side selected by a region accumulating at infinity is forced to be the genuine exterior. -/
theorem openHHalfPlane_circle_outside_of_trace_infty (S : Set ℍ)
    (hEnd : (∞ : OnePoint ℂ) ∈ hTraceIdealEndpoints S) (c r : ℝ) (hr : 0 < r) (m : ℍ)
    (hm : m ∉ (HalfPlaneLine.circle c r hr).carrier)
    (hsub : S ⊆ openHHalfPlane (.circle c r hr) m) :
    openHHalfPlane (.circle c r hr) m = {u : ℍ | r < ‖(u : ℂ)-(c : ℂ)‖} := by
  apply openHHalfPlane_circle_outside c r hr m
  have hne : ‖(m : ℂ)-(c : ℂ)‖ ≠ r := hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u,hu,hbig⟩ := hTraceIdealEndpoints_infty_unbounded S hEnd (c : ℂ) r
    have hsmall := openHHalfPlane_circle_inside_subset c r hr m hlt (hsub hu)
    exact (lt_asymm hbig hsmall).elim
  · exact hgt

theorem DiscLine.closedCarrier_ideal_iff_halfPlane (L : DiscLine) (p : 𝕔𝔻)
    (hp : ‖(p : ℂ)‖ = 1) :
    extendedCayley.symm (closedDiscToExtended p) ∈ L.toHalfPlane.idealEndpoints ↔ p ∈ L.closedCarrier := by
  rw [L.closedCarrier_mem_ideal_iff p hp,L.idealEndpoints_eq_cayley_image]
  constructor
  · intro h
    exact ⟨extendedCayley.symm (closedDiscToExtended p),h,extendedCayley.apply_symm_apply _⟩
  · rintro ⟨q,hq,he⟩
    simpa only [← he,extendedCayley.symm_apply_apply] using hq

/-- Every genuine ideal point admits a positive determinant-one normalizer, without finite-vertex assumptions. -/
theorem halfPlaneIdealBoundary_exists_sl2_to_infty (p : OnePoint ℂ) (hp : p ∈ halfPlaneIdealBoundary) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ s)) p = ∞ := by
  let R := HRayAt.canonical UpperHalfPlane.I p hp
  obtain ⟨s,_,he⟩ := R.exists_sl2_normalized_upward
  have hg : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ s).val.det := by
    change 0 < s.val.det
    rw [s.property]
    norm_num
  rw [R.realGLMap_idealEndpoint _ hg] at he
  have hR : R.idealEndpoint = p := R.idealEndpoint_unique (isHLineRay_hRay _ _ hp)
  rw [hR] at he
  exact ⟨s,he⟩

/-- The genuine affine map which fixes infinity and sends a given semicircle to the unit semicircle. -/
def circleToUnitNormalizer (c r : ℝ) (hr : 0 < r) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,-c;0,r] (by simpa [Matrix.det_fin_two] using hr.ne')

theorem circleToUnitNormalizer_pos (c r : ℝ) (hr : 0 < r) :
    0 < (circleToUnitNormalizer c r hr).val.det := by
  simpa [circleToUnitNormalizer,Matrix.det_fin_two] using hr

theorem circleToUnitNormalizer_coe (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (((circleToUnitNormalizer c r hr) • z : ℍ) : ℂ) = ((z : ℂ)-(c : ℂ))/(r : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (circleToUnitNormalizer_pos c r hr)]
  simp [circleToUnitNormalizer,UpperHalfPlane.num,UpperHalfPlane.denom,sub_eq_add_neg]

theorem circleToUnitNormalizer_infty (c r : ℝ) (hr : 0 < r) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix (circleToUnitNormalizer c r hr)) ∞ = ∞ := by
  rw [Mobius.fractionalLinear_infty]
  simp [complexifiedRealMobiusMatrix,circleToUnitNormalizer]

theorem circleToUnitNormalizer_mem (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    circleToUnitNormalizer c r hr • z ∈ (HalfPlaneLine.circle 0 1 (by norm_num)).carrier ↔
      z ∈ (HalfPlaneLine.circle c r hr).carrier := by
  change ‖(((circleToUnitNormalizer c r hr) • z : ℍ) : ℂ)-(0:ℂ)‖ = 1 ↔ _
  rw [sub_zero,circleToUnitNormalizer_coe,norm_div,Complex.norm_real,Real.norm_of_nonneg hr.le,
    div_eq_one_iff_eq hr.ne']
  rfl

theorem circleToUnitNormalizer_image (c r : ℝ) (hr : 0 < r) :
    (circleToUnitNormalizer c r hr • · : ℍ → ℍ) '' (HalfPlaneLine.circle c r hr).carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
  let g := circleToUnitNormalizer c r hr
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (circleToUnitNormalizer_mem c r hr w).mpr hw
  · intro hz
    refine ⟨g⁻¹ • z,?_,by change g • g⁻¹ • z = z; exact smul_inv_smul g z⟩
    apply (circleToUnitNormalizer_mem c r hr _).mp
    simpa only [show circleToUnitNormalizer c r hr = g from rfl,smul_inv_smul] using hz

/-- A line and any ideal point outside it admit the full unit-semicircle/infinity normalization. -/
theorem halfPlaneLine_ideal_point_normalizer (L : HalfPlaneLine) (p : OnePoint ℂ)
    (hp : p ∈ halfPlaneIdealBoundary) (hpL : p ∉ L.idealEndpoints) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p = ∞ ∧
      (g • · : ℍ → ℍ) '' L.carrier = (HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
  obtain ⟨s,hpEnd⟩ := halfPlaneIdealBoundary_exists_sl2_to_infty p hp
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by change 0 < s.val.det; rw [s.property]; norm_num
  obtain ⟨N,hN⟩ := realGL_image_hLine g L
  have hNE : N.idealEndpoints = Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' L.idealEndpoints := by
    change hTraceIdealEndpoints N.carrier = _
    rw [← hN,realGL_traceIdealEndpoints g hg]
    rfl
  have hnEnd : (∞ : OnePoint ℂ) ∉ N.idealEndpoints := by
    rw [hNE]
    rintro ⟨q,hq,he⟩
    have hqp : q = p := (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).injective
      (he.trans hpEnd.symm)
    exact hpL (hqp ▸ hq)
  cases N with
  | vertical a =>
    apply False.elim
    exact hnEnd (by rw [vertical_idealEndpoints]; exact mem_insert_of_mem _ (mem_singleton _))
  | circle c r hr =>
    let h := circleToUnitNormalizer c r hr
    have hh : 0 < h.val.det := circleToUnitNormalizer_pos c r hr
    refine ⟨h*g,?_,?_,?_⟩
    · change 0 < (h.val*g.val).det
      rw [Matrix.det_mul]
      exact mul_pos hh hg
    · change Mobius.fractionalLinear ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)) (h*g)) p = ∞
      rw [map_mul,Mobius.fractionalLinear_mul]
      change Mobius.fractionalLinear (complexifiedRealMobiusMatrix h)
        (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p) = ∞
      rw [show Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p = ∞ from hpEnd]
      exact circleToUnitNormalizer_infty c r hr
    · calc
        _ = (h • · : ℍ → ℍ) '' ((g • · : ℍ → ℍ) '' L.carrier) := by
          rw [image_image]
          apply image_congr
          intro z _
          exact mul_smul h g z
        _ = _ := by rw [hN]; exact circleToUnitNormalizer_image c r hr

end
end LowDimensionalTopology.Geometry.Hyperbolic
