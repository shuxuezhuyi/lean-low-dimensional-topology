/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ConvexTriangleFans
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicRayReturns
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual finite triangle and its actual ideal complement have disjoint interiors. -/
theorem ClosedDiscTriangle.idealComplement_interiors_disjoint (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hc : T.c∈closedModelDiscHSegment T.a w) (hcw : T.c≠w) :
    Disjoint T.interior (T.idealComplement w hc hcw).interior := by
  let U:=T.idealExtension w hc
  let V:=T.idealComplement w hc hcw
  obtain ⟨t,ht0,ht1,htc⟩:=T.idealExtension_coordinate w hc hcw
  have hLow:=T.halfPlaneInterior_split_lower U rfl rfl t ht0 htc
  have hHigh:=U.halfPlaneInterior_split_upper V rfl rfl t ht1 htc
  apply disjoint_left.mpr
  intro z hzT hzV
  have hmT : discToHalfPlane z∈T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hmV : discToHalfPlane z∈V.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈V.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hl:=(hLow _).mp hmT
  have hh:=(hHigh _).mp hmV
  exact (not_lt_of_gt hl.2.2) hh.2.2

/-- An actual finite point subdividing a real finite-to-ideal side sees at least a straight angle in every open convex region containing the true extended triangle. -/
theorem ClosedDiscTriangle.region_angle_ge_pi_of_ideal_subdivision (T : ClosedDiscTriangle)
    (w : 𝕔𝔻) (hw : ‖(w:ℂ)‖=1) (hcS : T.c∈closedModelDiscHSegment T.a w) (hcw : T.c≠w)
    (a b c : 𝔻) (ha : T.a=discToClosedModel a) (hb : T.b=discToClosedModel b)
    (hc : T.c=discToClosedModel c) {S : Set 𝔻} (hS : DiscHConvex S) (ho : IsOpen S)
    (hn : S.Nonempty) (haS : T.a∈_root_.closure (discToClosedModel '' S))
    (hbS : T.b∈_root_.closure (discToClosedModel '' S))
    (hcS' : T.c∈_root_.closure (discToClosedModel '' S))
    (hwS : w∈_root_.closure (discToClosedModel '' S)) :
    Real.pi ≤ discSubtendedAngle (_root_.closure S) c := by
  let V:=T.idealComplement w hcS hcw
  let F : Fin 2→ClosedDiscTriangle:=![T,V]
  have hz (i : Fin 2) : c∈(F i).finiteCarrier := by
    fin_cases i
    · change discToClosedModel c∈T.closedCarrier
      rw [←hc]
      exact subset_closedDiscHConvexHull _ (Or.inr (Or.inr rfl))
    · change discToClosedModel c∈V.closedCarrier
      rw [show discToClosedModel c=V.a from hc.symm]
      exact subset_closedDiscHConvexHull _ (Or.inl rfl)
  have hsub (i : Fin 2) : (F i).interior⊆S := by
    fin_cases i
    · exact T.interior_subset_of_vertices_mem_closedModelClosure hS ho hn haS hbS hcS'
    · exact V.interior_subset_of_vertices_mem_closedModelClosure hS ho hn hcS' hbS hwS
  have hd : Pairwise (fun i j=>Disjoint (F i).interior (F j).interior) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact T.idealComplement_interiors_disjoint w hcS hcw
    · exact (T.idealComplement_interiors_disjoint w hcS hcw).symm
    · exact (hij rfl).elim
  have he:=triangle_family_subtendedAngle_sum_le F c S hz hsub hd
  have hbgt : discSubtendedAngle T.finiteCarrier c+discSubtendedAngle V.finiteCarrier c ≤
      discSubtendedAngle (_root_.closure S) c := by
    simpa only [F,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using he
  rw [T.subtendedAngle_at_corner 2 c hc,V.subtendedAngle_at_finite c hc] at hbgt
  have hα:=T.idealComplement_alpha w hw hcS hcw a b c ha hb hc
  change V.alpha=Real.pi-T.gamma at hα
  rw [hα] at hbgt
  change T.gamma+(Real.pi-T.gamma) ≤ _ at hbgt
  linarith

/-- Every actual nonempty open half-plane region has a point off any prescribed vertical line. -/
theorem open_halfPlaneRegion_exists_re_ne {S : Set ℍ} (ho : IsOpen S) (hn : S.Nonempty) (r : ℝ) :
    ∃b∈S,b.re≠r := by
  obtain ⟨z,hz⟩:=hn
  by_cases hzre : z.re=r
  · let f : ℝ→ℍ:=fun t=>metricProbe t z.im z.im_pos
    have hf : Continuous f := by
      apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
      have he : (fun t : ℝ=>(⟨t,z.im⟩:ℂ))=(fun t : ℝ=>(t:ℂ)+(z.im:ℂ)*Complex.I) := by
        funext t
        exact Complex.ext (by simp) (by simp)
      change Continuous (fun t : ℝ=>(⟨t,z.im⟩:ℂ))
      rw [he]
      fun_prop
    have hfz : f z.re=z:=UpperHalfPlane.ext (Complex.ext rfl rfl)
    have hp : z.re∈f ⁻¹' S := by change f z.re∈S; rwa [hfz]
    obtain ⟨δ,hδ,hball⟩:=Metric.mem_nhds_iff.mp ((ho.preimage hf).mem_nhds hp)
    refine ⟨f (z.re+δ/2),hball ?_,?_⟩
    · rw [Metric.mem_ball,Real.dist_eq]
      rw [show z.re+δ/2-z.re=δ/2 by ring,abs_of_pos (by linarith)]
      linarith
    · change z.re+δ/2≠r
      rw [hzre]
      linarith
  · exact ⟨z,hz,hzre⟩

/-- A literal finite triangle with its first and third points on one vertical line and the third above the first is nondegenerate as soon as its second point is off that line. -/
def verticalSubdivisionHTriangle (a b c : ℍ) (hre : c.re=a.re) (him : a.im<c.im)
    (hb : b.re≠a.re) : ClosedHTriangle where
  a:=halfPlaneToClosedModel a
  b:=halfPlaneToClosedModel b
  c:=halfPlaneToClosedModel c
  noncollinear:=by
    rintro ⟨L,haL,hbL,hcL⟩
    have hac : a≠c:=by intro he;exact him.ne (congrArg UpperHalfPlane.im he)
    have hLa:=L.closedCarrier_mem_interior_iff a |>.mp haL
    have hLb:=L.closedCarrier_mem_interior_iff b |>.mp hbL
    have hLc:=L.closedCarrier_mem_interior_iff c |>.mp hcL
    have he:=L.eq_of_two_points (.vertical a.re) hac hLa hLc rfl hre
    rw [he] at hLb
    exact hb hLb

/-- The actual third point of the vertical subdivision lies on the genuine first-to-infinity compactified segment. -/
theorem verticalSubdivisionHTriangle_mem_idealSegment (a b c : ℍ) (hre : c.re=a.re)
    (him : a.im<c.im) (hb : b.re≠a.re) :
    (verticalSubdivisionHTriangle a b c hre him hb).toDiscTriangle.c∈
      closedModelDiscHSegment (verticalSubdivisionHTriangle a b c hre him hb).toDiscTriangle.a
        (closedModelCayleyHomeomorph twoIdealInfiniteEndpoint) := by
  have hR:=isHLineRay_hRay a (OnePoint.infty:OnePoint ℂ) twoIdealInfiniteEndpoint_ideal
  let R : HRayAt a:=⟨hRay a OnePoint.infty,OnePoint.infty,twoIdealInfiniteEndpoint_ideal,hR⟩
  have hEnd : R.idealEndpoint=OnePoint.infty:=R.idealEndpoint_unique hR
  have hcR : c∈hRay a OnePoint.infty :=
    (R.mem_iff_upward_of_endpoint_infty hEnd c).mpr ⟨hre,him.le⟩
  change halfPlaneToClosedModel c∈closedModelCayleyHomeomorph ⁻¹' closedModelDiscHSegment
    (closedModelCayleyHomeomorph (halfPlaneToClosedModel a))
    (closedModelCayleyHomeomorph twoIdealInfiniteEndpoint)
  rw [cayley_pullback_closed_segment_ray a twoIdealInfiniteEndpoint twoIdealInfiniteEndpoint_ideal]
  exact subset_closure ⟨c,hcR,rfl⟩

/-- Two actual finite closure points on the same vertical line force at least a straight genuine local angle at the higher point whenever infinity is also a true ideal closure point. No off-line witness or angle budget is assumed. -/
theorem discHConvex_region_angle_ge_pi_of_vertical_closure_points {S : Set 𝔻}
    (hS : DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S))
    (a c : ℍ) (hre : c.re=a.re) (him : a.im<c.im)
    (haS : discToClosedModel (halfPlaneToDisc a)∈_root_.closure (discToClosedModel '' S))
    (hcS : discToClosedModel (halfPlaneToDisc c)∈_root_.closure (discToClosedModel '' S)) :
    Real.pi ≤ discSubtendedAngle (_root_.closure S) (halfPlaneToDisc c) := by
  obtain ⟨b,hb,hbre⟩:=open_halfPlaneRegion_exists_re_ne
    (cayleyHomeomorph.symm.isOpenMap S ho) (hn.image discToHalfPlane) a.re
  have hbS : halfPlaneToDisc b∈S := by
    obtain ⟨z,hz,hzb⟩:=hb
    have hh : discToHalfPlane z=b:=hzb
    rwa [←hh,halfPlaneToDisc_discToHalfPlane]
  let T:=(verticalSubdivisionHTriangle a b c hre him hbre).toDiscTriangle
  let w:=closedModelCayleyHomeomorph twoIdealInfiniteEndpoint
  have hw : ‖(w:ℂ)‖=1:=closedModelCayley_ideal_norm _ twoIdealInfiniteEndpoint_ideal
  have hcSeg : T.c∈closedModelDiscHSegment T.a w:=
    verticalSubdivisionHTriangle_mem_idealSegment a b c hre him hbre
  have hcw : T.c≠w := by
    intro he
    have hh:=closedModelCayleyHomeomorph.injective he
    exact OnePoint.coe_ne_infty (c:ℂ) (congrArg Subtype.val hh)
  have hA : T.a=discToClosedModel (halfPlaneToDisc a):=closedModelCayley_on_interior a
  have hB : T.b=discToClosedModel (halfPlaneToDisc b):=closedModelCayley_on_interior b
  have hC : T.c=discToClosedModel (halfPlaneToDisc c):=closedModelCayley_on_interior c
  apply T.region_angle_ge_pi_of_ideal_subdivision w hw hcSeg hcw
    (halfPlaneToDisc a) (halfPlaneToDisc b) (halfPlaneToDisc c) hA hB hC hS ho hn
  · rwa [hA]
  · rw [hB]
    exact subset_closure (mem_image_of_mem discToClosedModel hbS)
  · rwa [hC]
  · exact hi

/-- All genuine finite closure points with local angle strictly below pi have distinct real coordinates when infinity is an actual ideal closure point. -/
theorem discHConvex_proper_corners_re_injOn {S : Set 𝔻}
    (hS : DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S)) :
    Set.InjOn (fun z : ℍ=>z.re) {z : ℍ |
      discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S) ∧
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z)<Real.pi} := by
  intro a ha c hc hre
  by_contra hne
  have him : a.im≠c.im:=by
    intro he
    exact hne (UpperHalfPlane.ext (Complex.ext hre he))
  rcases lt_or_gt_of_ne him with hlt|hlt
  · exact (not_lt_of_ge (discHConvex_region_angle_ge_pi_of_vertical_closure_points
      hS ho hn hi a c hre.symm hlt ha.1 hc.1)) hc.2
  · exact (not_lt_of_ge (discHConvex_region_angle_ge_pi_of_vertical_closure_points
      hS ho hn hi c a hre hlt hc.1 ha.1)) ha.2

/-- A finite set of genuine strictly convex closure corners has total true angle deficit controlled by the actual density area. The real-coordinate ordering is constructed rather than assumed. -/
theorem finite_proper_corner_angle_deficit_bound {S : Set 𝔻}
    (hS : DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S))
    (X : Finset ℍ) (hX : ∀z∈X,
      discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S) ∧
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z)<Real.pi) :
    (∑z∈X,(Real.pi-discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z))) ≤
      (discHyperbolicArea S).toReal+Real.pi := by
  classical
  by_cases hne : X.Nonempty
  · let θ (z : ℍ):=discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z)
    have hinj : Function.Injective (fun z : X=>z.val.re) := by
      intro a b hab
      apply Subtype.ext
      exact discHConvex_proper_corners_re_injOn hS ho hn hi
        (hX a.val a.property) (hX b.val b.property) hab
    let : LinearOrder X:=LinearOrder.lift' (fun z : X=>z.val.re) hinj
    let n:=X.card-1
    have hc : n+1=X.card:=by have:=Finset.card_pos.mpr hne;dsimp [n];omega
    let e : Fin (n+1)≃oX:=Fintype.orderIsoFinOfCardEq X (by simpa only [Fintype.card_coe] using hc.symm)
    have horder : StrictMono (fun i : Fin (n+1)=>(e i).val.re):=e.strictMono
    have hb:=finiteHPointFan_area_angle_budget (fun i=>(e i).val) horder hS ho hn harea
      (fun i=>(hX (e i).val (e i).property).1) hi
    have hs : (∑i : Fin (n+1),θ (e i).val)=∑z∈X,θ z :=
      (e.toEquiv.sum_comp (fun z : X=>θ z.val)).trans
        (Finset.sum_subtype X (by intro z;rfl) θ).symm
    change (n:ℝ)*Real.pi ≤ (discHyperbolicArea S).toReal+∑i : Fin (n+1),θ (e i).val at hb
    rw [hs] at hb
    have hcR : (n:ℝ)+1=(X.card:ℝ):=by exact_mod_cast hc
    change (∑z∈X,(Real.pi-θ z)) ≤ _
    rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    have hcπ : (X.card:ℝ)*Real.pi=(n:ℝ)*Real.pi+Real.pi := by rw [←hcR];ring
    rw [hcπ]
    linarith only [hb]
  · have he : X=∅:=Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    positivity

/-- Straight closure points have zero deficit, so the quantitative true area bound holds for every finite set of genuine nonreflex closure corners, with no real-order or injectivity hypothesis. -/
theorem finite_corner_angle_deficit_bound {S : Set 𝔻}
    (hS : DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤)
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S))
    (X : Finset ℍ) (hX : ∀z∈X,
      discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S) ∧
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z) ≤ Real.pi) :
    (∑z∈X,(Real.pi-discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z))) ≤
      (discHyperbolicArea S).toReal+Real.pi := by
  classical
  let θ (z : ℍ):=discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z)
  let Y:=X.filter (fun z=>θ z<Real.pi)
  have hY (z : ℍ) (hz : z∈Y) :
      discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S) ∧ θ z<Real.pi :=
    ⟨(hX z (Finset.mem_filter.mp hz).1).1,(Finset.mem_filter.mp hz).2⟩
  have hb:=finite_proper_corner_angle_deficit_bound hS ho hn harea hi Y hY
  have he : (∑z∈Y,(Real.pi-θ z))=∑z∈X,(Real.pi-θ z) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hzY
    have hnot : ¬θ z<Real.pi:=by simpa only [Y,Finset.mem_filter,hz,true_and] using hzY
    have hθ : θ z=Real.pi:=le_antisymm (hX z hz).2 (le_of_not_gt hnot)
    rw [hθ,sub_self]
  change (∑z∈Y,(Real.pi-θ z)) ≤ _ at hb
  rw [he] at hb
  exact hb

/-- The same actual finite-corner deficit bound holds with an arbitrary genuine ideal closure point; its determinant-one infinity normalizer is constructed and actual density area and angles are transported. -/
theorem finite_corner_angle_deficit_bound_of_ideal {S : Set 𝔻}
    (hS : DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤)
    (p : 𝕔𝔻) (hp : p∈discIdealClosureTrace S) (X : Finset ℍ)
    (hX : ∀z∈X,discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S) ∧
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z) ≤ Real.pi) :
    (∑z∈X,(Real.pi-discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z))) ≤
      (discHyperbolicArea S).toReal+Real.pi := by
  classical
  obtain ⟨s,hs⟩:=discIdealPoint_exists_SL_normalizer p hp.2
  let F:=discSL2Homeomorph s
  let e:=idealFanSLIsometry s
  let S':=F '' S
  have hF : let :=discHyperbolicMetric;Isometry F := by
    let :=discHyperbolicMetric
    change Isometry (discSL2Action s)
    exact discSL2Action_isometry s
  have he : e.finiteMap '' S=S':=rfl
  have hc : DiscHConvex S':=hS.isometry_image hF
  have ho' : IsOpen S':=F.isOpenMap S ho
  have hn' : S'.Nonempty:=hn.image F
  have hArea : discHyperbolicArea S'=discHyperbolicArea S:=discSL2Equiv_area s S ho.measurableSet
  have hArea' : discHyperbolicArea S'≠⊤:=by rwa [hArea]
  have hi' : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S') := by
    have hh : e.closedMap p∈discIdealClosureTrace S' := by
      rw [←he,←e.image_discIdealClosureTrace S]
      exact mem_image_of_mem _ hp
    rw [show e.closedMap p=closedModelCayleyHomeomorph twoIdealInfiniteEndpoint from hs] at hh
    exact hh.1
  have hfinite (z : ℍ) : F (halfPlaneToDisc z)=halfPlaneToDisc (s•z) := by
    change halfPlaneToDisc (s•discToHalfPlane (halfPlaneToDisc z))=_
    rw [discToHalfPlane_halfPlaneToDisc]
  have hAngle (z : ℍ) : discSubtendedAngle (_root_.closure S') (halfPlaneToDisc (s•z))=
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc z) := by
    have hh:=discSubtendedAngle_isometry F hF (_root_.closure S) (halfPlaneToDisc z)
    rw [F.image_closure,hfinite] at hh
    exact hh
  have hClosure : e.closedMap '' _root_.closure (discToClosedModel '' S)=
      _root_.closure (discToClosedModel '' S') := by
    rw [e.closedMap.image_closure,e.closedMap_image_finite,he]
  have hpoint (z : ℍ) : e.closedMap (discToClosedModel (halfPlaneToDisc z))=
      discToClosedModel (halfPlaneToDisc (s•z)) := by
    rw [e.finite_commutes]
    exact congrArg discToClosedModel (hfinite z)
  let f : ℍ↪ℍ:=⟨(s•·),(isometry_smul ℍ s).injective⟩
  let Y:=X.map f
  have hY (z : ℍ) (hz : z∈Y) :
      discToClosedModel (halfPlaneToDisc z)∈_root_.closure (discToClosedModel '' S') ∧
      discSubtendedAngle (_root_.closure S') (halfPlaneToDisc z) ≤ Real.pi := by
    obtain ⟨a,ha,rfl⟩:=Finset.mem_map.mp hz
    constructor
    · change discToClosedModel (halfPlaneToDisc (s•a))∈_
      rw [←hpoint]
      exact hClosure ▸ mem_image_of_mem e.closedMap (hX a ha).1
    · change discSubtendedAngle (_root_.closure S') (halfPlaneToDisc (s•a)) ≤ _
      rw [hAngle]
      exact (hX a ha).2
  have hb:=finite_corner_angle_deficit_bound hc ho' hn' hArea' hi' Y hY
  change (∑z∈X.map f,(Real.pi-discSubtendedAngle (_root_.closure S') (halfPlaneToDisc z))) ≤ _ at hb
  rw [Finset.sum_map] at hb
  change (∑z∈X,(Real.pi-discSubtendedAngle (_root_.closure S') (halfPlaneToDisc (s•z)))) ≤ _ at hb
  simp_rw [hAngle] at hb
  rwa [hArea] at hb

end LowDimensionalTopology.Geometry.Hyperbolic
