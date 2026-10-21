/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaIntegrals
@[expose] public section
open Set MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- Normalize a genuine ideal vertex and its opposite actual side-line, without finite-vertex assumptions. -/
theorem ClosedDiscTriangle.exists_ideal_vertex_area_normalizer (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) = ∞ ∧
      (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
        (HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
  have hp : extendedCayley.symm (closedDiscToExtended T.c) ∈ halfPlaneIdealBoundary := by
    rw [idealBoundary_cayley_iff,extendedCayley.apply_symm_apply]
    simpa only [closedDiscToExtended,coe_mem_extendedDiscIdealBoundary] using hc
  have hpL : extendedCayley.symm (closedDiscToExtended T.c) ∉ T.sideLineC.toHalfPlane.idealEndpoints := by
    intro h
    exact T.c_not_mem_sideLineC ((T.sideLineC.closedCarrier_ideal_iff_halfPlane T.c hc).mp h)
  exact halfPlaneLine_ideal_point_normalizer T.sideLineC.toHalfPlane _ hp hpL

/-- Infinity accumulation forces the whole normalized triangle onto the outside of its unit semicircle. -/
theorem ClosedDiscTriangle.normalized_interior_circle_outside (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (m : ℍ) (hm : m ∈ T.halfPlaneInterior) :
    1 < ‖((g • m : ℍ) : ℂ)‖ ∧
      (g • · : ℍ → ℍ) '' T.halfPlaneInterior ⊆ {z : ℍ | 1 < ‖(z : ℂ)‖} := by
  have hcc : T.c ∈ T.closedCarrier := subset_closedDiscHConvexHull _ (by simp)
  have hEnd : (∞ : OnePoint ℂ) ∈ hTraceIdealEndpoints ((g • · : ℍ → ℍ) '' T.halfPlaneInterior) := by
    rw [realGL_traceIdealEndpoints g hg]
    exact ⟨extendedCayley.symm (closedDiscToExtended T.c),T.idealPoint_mem_traceInterior T.c hcc hc,hpEnd⟩
  have hno : m ∉ T.sideLineC.toHalfPlane.carrier := by
    intro h
    have he := (T.halfPlaneCoordinate_first_line m).mpr h
    have hp := (T.mem_halfPlaneInterior_iff m).mp hm
    linarith only [he,hp.2.1]
  have hno' : g • m ∉ (HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
    intro h
    rw [← hline] at h
    exact hno ((realGL_isometry g).injective.mem_set_image.mp h)
  have hsub : (g • · : ℍ → ℍ) '' T.halfPlaneInterior ⊆
      openHHalfPlane (.circle 0 1 (by norm_num)) (g • m) := by
    rw [← realGL_image_openHalfPlane g T.sideLineC.toHalfPlane _ hline m hno]
    apply image_mono
    rw [T.halfPlaneInterior_eq_components m hm]
    exact fun _ hx => hx.2.2
  have hout := openHHalfPlane_circle_outside_of_trace_infty _ hEnd 0 1 (by norm_num) (g • m) hno' hsub
  have hall : (g • · : ℍ → ℍ) '' T.halfPlaneInterior ⊆ {z : ℍ | 1 < ‖(z : ℂ)‖} := by
    intro z hz
    have he := hsub hz
    rw [hout] at he
    simpa using he
  exact ⟨hall (mem_image_of_mem (g • ·) hm),hall⟩

theorem realGL_image_idealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (L M : HalfPlaneLine) (hline : (g • · : ℍ → ℍ) '' L.carrier = M.carrier) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' L.idealEndpoints = M.idealEndpoints := by
  change _ = hTraceIdealEndpoints M.carrier
  rw [← hline,realGL_traceIdealEndpoints g hg]
  rfl

/-- Any closed-model point of the normalized opposite side has a genuine finite upper-semicircle coordinate. -/
theorem realGL_closedLine_point_unitCircle (L : DiscLine) (p : 𝕔𝔻) (hp : p ∈ L.closedCarrier)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hline : (g • · : ℍ → ℍ) '' L.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ 0 ≤ a.im ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) = (a :
        OnePoint ℂ) := by
  rcases closedDisc_interior_or_ideal p with ⟨z,hz⟩ | hideal
  · have hzL : discToHalfPlane z ∈ L.toHalfPlane.carrier := by
      apply (L.mem_carrier z).mp
      apply (L.closedCarrier_mem_interior_iff z).mp
      rwa [hz]
    have hgzL := hline ▸ mem_image_of_mem (g • · : ℍ → ℍ) hzL
    refine ⟨((g • discToHalfPlane z : ℍ) : ℂ),?_,(g • discToHalfPlane z).im_pos.le,?_⟩
    · change ‖((g • discToHalfPlane z : ℍ) : ℂ)-(0:ℂ)‖ = 1 at hgzL
      simpa only [sub_zero] using hgzL
    · rw [← hz]
      change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm ((z : ℂ) : OnePoint ℂ)) = _
      rw [extendedCayley_symm_coe_disc]
      exact realMobiusMatrix_coe g hg (discToHalfPlane z)
  · have hpE := (L.closedCarrier_ideal_iff_halfPlane p hideal).mpr hp
    have hE := realGL_image_idealEndpoints g hg L.toHalfPlane _ hline
    have hgp : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) ∈
        (HalfPlaneLine.circle 0 1 (by norm_num)).idealEndpoints :=
      hE ▸ mem_image_of_mem (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) hpE
    rw [circle_idealEndpoints] at hgp
    norm_num at hgp
    rcases hgp with h | h
    · exact ⟨-1,by norm_num,by norm_num,h⟩
    · exact ⟨1,by norm_num,by norm_num,h⟩

/-- A finite complex value of a closed line point fixes the real coordinate of a normalized vertical line. -/
theorem realGL_closedLine_point_vertical_re (L : DiscLine) (p : 𝕔𝔻) (hp : p ∈ L.closedCarrier)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (k : ℝ)
    (hline : (g • · : ℍ → ℍ) '' L.toHalfPlane.carrier = (HalfPlaneLine.vertical k).carrier)
    (b : ℂ) (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)
      (extendedCayley.symm (closedDiscToExtended p)) = (b : OnePoint ℂ)) : b.re = k := by
  rcases closedDisc_interior_or_ideal p with ⟨z,hz⟩ | hideal
  · have hzL : discToHalfPlane z ∈ L.toHalfPlane.carrier := by
      apply (L.mem_carrier z).mp
      apply (L.closedCarrier_mem_interior_iff z).mp
      rwa [hz]
    have hgzL := hline ▸ mem_image_of_mem (g • · : ℍ → ℍ) hzL
    have hfg : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) =
        ((((g • discToHalfPlane z : ℍ) : ℂ)) : OnePoint ℂ) := by
      rw [← hz]
      change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm ((z : ℂ) : OnePoint ℂ)) = _
      rw [extendedCayley_symm_coe_disc]
      exact realMobiusMatrix_coe g hg (discToHalfPlane z)
    have hqb : ((g • discToHalfPlane z : ℍ) : ℂ) = b := OnePoint.coe_injective (hfg.symm.trans hb)
    change (g • discToHalfPlane z).re = k at hgzL
    simpa only [← hqb,UpperHalfPlane.coe_re] using hgzL
  · have hpE := (L.closedCarrier_ideal_iff_halfPlane p hideal).mpr hp
    have hE := realGL_image_idealEndpoints g hg L.toHalfPlane _ hline
    have hgp : (b : OnePoint ℂ) ∈ (HalfPlaneLine.vertical k).idealEndpoints := by
      rw [← hE,← hb]
      exact mem_image_of_mem (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) hpE
    rw [vertical_idealEndpoints] at hgp
    rcases hgp with h | h
    · have he : b = (k : ℂ) := OnePoint.coe_injective h
      simp only [he,Complex.ofReal_re]
    · exact (OnePoint.coe_ne_infty b (mem_singleton_iff.mp h)).elim

/-- Mapping an actual ideal endpoint to infinity makes its incident line genuinely vertical. -/
theorem realGL_closedLine_image_vertical_of_ideal (L : DiscLine) (p : 𝕔𝔻)
    (hp : p ∈ L.closedCarrier) (hideal : ‖(p : ℂ)‖ = 1)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) =
      ∞) :
    ∃ k : ℝ, (g • · : ℍ → ℍ) '' L.toHalfPlane.carrier = (HalfPlaneLine.vertical k).carrier := by
  obtain ⟨N,hN⟩ := realGL_image_hLine g L.toHalfPlane
  have hpE := (L.closedCarrier_ideal_iff_halfPlane p hideal).mpr hp
  have hE := realGL_image_idealEndpoints g hg L.toHalfPlane N hN
  have hgp : (∞ : OnePoint ℂ) ∈ N.idealEndpoints := by
    rw [← hE,← hpEnd]
    exact mem_image_of_mem (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) hpE
  cases N with
  | vertical k => exact ⟨k,hN⟩
  | circle c r hr => simp [circle_idealEndpoints] at hgp

theorem unitUpperCircle_re_injective {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hia : 0 ≤ a.im) (hib : 0 ≤ b.im) (hre : a.re = b.re) : a = b := by
  have hA := Complex.normSq_eq_norm_sq a
  have hB := Complex.normSq_eq_norm_sq b
  rw [ha,one_pow,Complex.normSq_apply] at hA
  rw [hb,one_pow,Complex.normSq_apply] at hB
  rw [hre] at hA
  have him : a.im = b.im := (sq_eq_sq₀ hia hib).mp (by nlinarith only [hA,hB])
  exact Complex.ext hre him

/-- Both remaining genuine vertices acquire finite upper-unit-circle coordinates, and both incident sides become the correct vertical lines. -/
theorem ClosedDiscTriangle.normalized_sides_and_vertices (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ 0 ≤ a.im ∧ 0 ≤ b.im ∧ a.re ≠ b.re ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a :
        OnePoint ℂ) ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b :
        OnePoint ℂ) ∧
      (g • · : ℍ → ℍ) '' T.sideLineA.toHalfPlane.carrier = (HalfPlaneLine.vertical b.re).carrier ∧
      (g • · : ℍ → ℍ) '' T.sideLineB.toHalfPlane.carrier = (HalfPlaneLine.vertical a.re).carrier := by
  obtain ⟨a,hna,hia,ha⟩ := realGL_closedLine_point_unitCircle T.sideLineC T.a T.a_mem_sideLineC g hg hline
  obtain ⟨b,hnb,hib,hb⟩ := realGL_closedLine_point_unitCircle T.sideLineC T.b T.b_mem_sideLineC g hg hline
  have hab : a ≠ b := by
    intro he
    apply T.a_ne_b
    apply isEmbedding_closedDiscToExtended.injective
    apply extendedCayley.symm.injective
    apply (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).injective
    exact ha.trans ((congrArg ((↑) : ℂ → OnePoint ℂ) he).trans hb.symm)
  have hre : a.re ≠ b.re := fun he => hab (unitUpperCircle_re_injective hna hnb hia hib he)
  obtain ⟨k,hA⟩ := realGL_closedLine_image_vertical_of_ideal T.sideLineA T.c T.c_mem_sideLineA hc g hg hpEnd
  obtain ⟨l,hB⟩ := realGL_closedLine_image_vertical_of_ideal T.sideLineB T.c T.c_mem_sideLineB hc g hg hpEnd
  have hk : b.re = k := realGL_closedLine_point_vertical_re T.sideLineA T.b T.b_mem_sideLineA g hg k hA b hb
  have hl : a.re = l := realGL_closedLine_point_vertical_re T.sideLineB T.a T.a_mem_sideLineB g hg l hB a ha
  refine ⟨a,b,hna,hnb,hia,hib,hre,ha,hb,?_,?_⟩
  · rwa [← hk] at hA
  · rwa [← hl] at hB

/-- All actual closed-triangle points, including finite vertices, are ambient closure points of its interior. -/
theorem ClosedDiscTriangle.closedPoint_mem_closureInterior (T : ClosedDiscTriangle)
    (p : 𝕔𝔻) (hp : p ∈ T.closedCarrier) :
    extendedCayley.symm (closedDiscToExtended p) ∈
      closure (extendedHalfPlanePoint '' T.halfPlaneInterior) := by
  have hpC : (p : ℂ) ∈ closure (((↑) : 𝔻 → ℂ) '' T.interior) := by
    rw [T.interior_complex_image,T.complexInterior_closure]
    exact ⟨p,hp,rfl⟩
  have he : closedDiscToExtended p ∈ closure (extendedDiscPoint '' T.interior) := by
    change ((p : ℂ) : OnePoint ℂ) ∈ closure ((fun z : 𝔻 => ((z : ℂ) : OnePoint ℂ)) '' T.interior)
    have hi := image_closure_subset_closure_image OnePoint.continuous_coe
      (mem_image_of_mem ((↑) : ℂ → OnePoint ℂ) hpC)
    simpa only [image_image] using hi
  have hmem := mem_image_of_mem extendedCayley.symm he
  rw [extendedCayley.symm.image_closure,image_image] at hmem
  simp_rw [extendedDiscPoint,extendedCayley_symm_coe_disc] at hmem
  rw [← image_image,T.discToHalfPlane_image_interior] at hmem
  exact hmem

/-- Finite points in the ambient compactified closure retain every ordinary closed Euclidean constraint. -/
theorem finite_mem_extended_closure_mem_closed (S : Set ℍ) (K : Set ℂ) (hK : IsClosed K)
    (hsub : ((↑) : ℍ → ℂ) '' S ⊆ K) (a : ℂ)
    (ha : (a : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S)) : a ∈ K := by
  have hi : extendedHalfPlanePoint '' S = ((↑) : ℂ → OnePoint ℂ) '' (((↑) : ℍ → ℂ) '' S) := by
    rw [image_image]
    rfl
  rw [hi] at ha
  have haC : a ∈ closure (((↑) : ℍ → ℂ) '' S) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
    exact ha
  exact closure_minimal hsub hK haC

/-- The actual right-hand vertical component, with its orientation determined by a finite witness. -/
theorem openHHalfPlane_vertical_gt (k : ℝ) (m : ℍ) (hm : k < m.re) :
    openHHalfPlane (.vertical k) m = {z : ℍ | k < z.re} := by
  have hpre : IsPreconnected {z : ℍ | k < z.re} := by
    apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
    have hi : ((↑) : ℍ → ℂ) '' {z : ℍ | k < z.re} =
        {z : ℂ | 0 < z.im} ∩ {z | k < z.re} := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨w.im_pos,hw⟩
      · rintro ⟨hz,hx⟩
        exact ⟨⟨z,hz⟩,hx,rfl⟩
    rw [hi]
    exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter
      (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear k)).isPreconnected
  have hmN : m ∈ (HalfPlaneLine.vertical k).carrierᶜ := ne_of_gt hm
  apply subset_antisymm
  · intro u hu
    have hp := (isPreconnected_connectedComponentIn
      (F := (HalfPlaneLine.vertical k).carrierᶜ) (x := m)).image UpperHalfPlane.re
      UpperHalfPlane.continuous_re.continuousOn
    have hmI := mem_image_of_mem UpperHalfPlane.re (mem_connectedComponentIn hmN)
    have huI := mem_image_of_mem UpperHalfPlane.re hu
    change k < u.re
    by_contra! hle
    obtain ⟨v,hv,he⟩ := hp.ordConnected.out huI hmI (show k ∈ Icc u.re m.re from ⟨hle,hm.le⟩)
    exact connectedComponentIn_subset (HalfPlaneLine.vertical k).carrierᶜ m hv he
  · apply hpre.subset_connectedComponentIn hm
    exact fun u hu => ne_of_gt hu

/-- The two distinct finite closure values force the base point between the actual vertical sides. -/
theorem vertical_components_position_of_closure (S : Set ℍ) (a b : ℂ) (hab : a.re < b.re)
    (ha : (a : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S))
    (hb : (b : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S)) (m : ℍ)
    (hma : m.re ≠ a.re) (hmb : m.re ≠ b.re)
    (hsa : S ⊆ openHHalfPlane (.vertical a.re) m)
    (hsb : S ⊆ openHHalfPlane (.vertical b.re) m) : a.re < m.re ∧ m.re < b.re := by
  constructor
  · by_contra! hn
    have hm : m.re < a.re := lt_of_le_of_ne hn hma
    have hsub : ((↑) : ℍ → ℂ) '' S ⊆ {z : ℂ | z.re ≤ a.re} := by
      rintro _ ⟨z,hz,rfl⟩
      have he := hsa hz
      rw [hReCutLt_eq_openHalfPlane a.re m hm] at he
      change z.re < a.re at he
      exact he.le
    have hclosed : IsClosed {z : ℂ | z.re ≤ a.re} := isClosed_le Complex.continuous_re continuous_const
    have he := finite_mem_extended_closure_mem_closed S _ hclosed hsub b hb
    change b.re ≤ a.re at he
    exact (not_le_of_gt hab) he
  · by_contra! hn
    have hm : b.re < m.re := lt_of_le_of_ne hn hmb.symm
    have hsub : ((↑) : ℍ → ℂ) '' S ⊆ {z : ℂ | b.re ≤ z.re} := by
      rintro _ ⟨z,hz,rfl⟩
      have he := hsb hz
      rw [openHHalfPlane_vertical_gt b.re m hm] at he
      change b.re < z.re at he
      exact he.le
    have hclosed : IsClosed {z : ℂ | b.re ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have he := finite_mem_extended_closure_mem_closed S _ hclosed hsub a ha
    change b.re ≤ a.re at he
    exact (not_le_of_gt hab) he

theorem unitCircle_outside_iff_sqrt_lt (z : ℍ) (hx : |z.re| < 1) :
    1 < ‖(z : ℂ)‖ ↔ Real.sqrt (1-z.re^2) < z.im := by
  have hpos : 0 < 1-z.re^2 := by
    have ht := abs_lt.mp hx
    nlinarith only [mul_pos (by linarith only [ht.1] : 0 < 1+z.re)
      (by linarith only [ht.2] : 0 < 1-z.re)]
  have hn := Complex.normSq_eq_norm_sq (z : ℂ)
  rw [Complex.normSq_apply] at hn
  simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] at hn
  have hs := Real.sq_sqrt hpos.le
  constructor
  · intro h
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) z.im_pos.le).mp
    nlinarith only [hn,hs,mul_pos (by linarith only [h] : 0 < ‖(z : ℂ)‖-1)
      (by linarith only [h] : 0 < ‖(z : ℂ)‖+1)]
  · intro h
    apply (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 1) (norm_nonneg _)).mp
    nlinarith only [hn,hs,mul_pos (sub_pos.mpr h)
      (add_pos_of_pos_of_nonneg z.im_pos (Real.sqrt_nonneg (1-z.re^2)))]

theorem vertical_unitCircle_components_eq_graph_ordered (S : Set ℍ) (a b : ℂ)
    (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hab : a.re < b.re)
    (ha : (a : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S))
    (hb : (b : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S)) (m : ℍ)
    (hma : m.re ≠ a.re) (hmb : m.re ≠ b.re)
    (hEq : S = openHHalfPlane (.vertical a.re) m ∩
      (openHHalfPlane (.vertical b.re) m ∩ {z : ℍ | 1 < ‖(z : ℂ)‖})) :
    S = halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo a.re b.re) := by
  have hsa : S ⊆ openHHalfPlane (.vertical a.re) m := fun _ hu => (hEq ▸ hu).1
  have hsb : S ⊆ openHHalfPlane (.vertical b.re) m := fun _ hu => (hEq ▸ hu).2.1
  obtain ⟨hlo,hhi⟩ := vertical_components_position_of_closure S a b hab ha hb m hma hmb hsa hsb
  have har : |a.re| ≤ 1 := by simpa only [hna] using Complex.abs_re_le_norm a
  have hbr : |b.re| ≤ 1 := by simpa only [hnb] using Complex.abs_re_le_norm b
  have hx {z : ℍ} (hl : a.re < z.re) (hu : z.re < b.re) : |z.re| < 1 :=
    abs_lt.mpr ⟨lt_of_le_of_lt (abs_le.mp har).1 hl,lt_of_lt_of_le hu (abs_le.mp hbr).2⟩
  rw [hEq,openHHalfPlane_vertical_gt a.re m hlo,hReCutLt_eq_openHalfPlane b.re m hhi]
  ext z
  change (a.re < z.re ∧ z.re < b.re ∧ 1 < ‖(z : ℂ)‖) ↔
    ((a.re < z.re ∧ z.re < b.re) ∧ Real.sqrt (1-z.re^2) < z.im)
  constructor
  · rintro ⟨hl,hu,hn⟩
    exact ⟨⟨hl,hu⟩,(unitCircle_outside_iff_sqrt_lt z (hx hl hu)).mp hn⟩
  · rintro ⟨⟨hl,hu⟩,hn⟩
    exact ⟨hl,hu,(unitCircle_outside_iff_sqrt_lt z (hx hl hu)).mpr hn⟩

theorem vertical_unitCircle_components_eq_graph (S : Set ℍ) (a b : ℂ)
    (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : (a : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S))
    (hb : (b : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' S)) (m : ℍ)
    (hma : m.re ≠ a.re) (hmb : m.re ≠ b.re)
    (hEq : S = openHHalfPlane (.vertical a.re) m ∩
      (openHHalfPlane (.vertical b.re) m ∩ {z : ℍ | 1 < ‖(z : ℂ)‖})) :
    S = halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo (min a.re b.re) (max a.re b.re)) := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · simpa only [min_eq_left hab.le,max_eq_right hab.le] using
      vertical_unitCircle_components_eq_graph_ordered S a b hna hnb hab ha hb m hma hmb hEq
  · have hEq' : S = openHHalfPlane (.vertical b.re) m ∩
        (openHHalfPlane (.vertical a.re) m ∩ {z : ℍ | 1 < ‖(z : ℂ)‖}) := by
      rw [hEq]
      ext z
      simp only [mem_inter_iff]
      tauto
    simpa only [min_eq_right hba.le,max_eq_left hba.le] using
      vertical_unitCircle_components_eq_graph_ordered S b a hnb hna hba hb ha m hmb hma hEq'

/-- The entire normalized genuine ideal triangle, including boundary-vertex cases, is the measured graph region. -/
theorem ClosedDiscTriangle.normalized_interior_eq_graph (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (a b : ℂ) (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ))
    (hA : (g • · : ℍ → ℍ) '' T.sideLineA.toHalfPlane.carrier = (HalfPlaneLine.vertical b.re).carrier)
    (hB : (g • · : ℍ → ℍ) '' T.sideLineB.toHalfPlane.carrier = (HalfPlaneLine.vertical a.re).carrier) :
    (g • · : ℍ → ℍ) '' T.halfPlaneInterior =
      halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo (min a.re b.re) (max a.re b.re)) := by
  obtain ⟨z,hz⟩ := T.interior_nonempty
  let m := discToHalfPlane z
  have hm : m ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hp := (T.mem_halfPlaneInterior_iff m).mp hm
  have hnoA : m ∉ T.sideLineA.toHalfPlane.carrier := by
    intro h
    have he := (T.halfPlaneCoordinate_opposite_line m).mpr h
    linarith only [he,hp.2.2]
  have hnoB : m ∉ T.sideLineB.toHalfPlane.carrier := by
    intro h
    have he := (T.halfPlaneCoordinate_second_line m).mpr h
    linarith only [he,hp.1]
  have hnoC : m ∉ T.sideLineC.toHalfPlane.carrier := by
    intro h
    have he := (T.halfPlaneCoordinate_first_line m).mpr h
    linarith only [he,hp.2.1]
  have hma : (g • m).re ≠ a.re := by
    intro h
    have he : g • m ∈ (HalfPlaneLine.vertical a.re).carrier := h
    rw [← hB] at he
    exact hnoB ((realGL_isometry g).injective.mem_set_image.mp he)
  have hmb : (g • m).re ≠ b.re := by
    intro h
    have he : g • m ∈ (HalfPlaneLine.vertical b.re).carrier := h
    rw [← hA] at he
    exact hnoA ((realGL_isometry g).injective.mem_set_image.mp he)
  have hnorm := (T.normalized_interior_circle_outside hc g hg hpEnd hline m hm).1
  have hout : openHHalfPlane (.circle 0 1 (by norm_num)) (g • m) = {u : ℍ | 1 < ‖(u : ℂ)‖} := by
    simpa using openHHalfPlane_circle_outside 0 1 (by norm_num) (g • m) (by simpa using hnorm)
  have hclosure (p : 𝕔𝔻) (hp : p ∈ T.closedCarrier) (c : ℂ)
      (hval : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) =
        (c : OnePoint ℂ)) :
      (c : OnePoint ℂ) ∈ closure (extendedHalfPlanePoint '' ((g • · : ℍ → ℍ) '' T.halfPlaneInterior)) := by
    have he := mem_image_of_mem (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g))
      (T.closedPoint_mem_closureInterior p hp)
    rw [Homeomorph.image_closure] at he
    change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended p)) ∈
      closure (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' (extendedHalfPlanePoint ''
        T.halfPlaneInterior)) at he
    rwa [hval,← realGL_extended_image g hg] at he
  have haC := hclosure T.a (subset_closedDiscHConvexHull _ (by simp)) a ha
  have hbC := hclosure T.b (subset_closedDiscHConvexHull _ (by simp)) b hb
  have hEq : (g • · : ℍ → ℍ) '' T.halfPlaneInterior = openHHalfPlane (.vertical a.re) (g • m) ∩
      (openHHalfPlane (.vertical b.re) (g • m) ∩ {u : ℍ | 1 < ‖(u : ℂ)‖}) := by
    rw [T.halfPlaneInterior_eq_components m hm,image_inter (realGL_isometry g).injective,
      image_inter (realGL_isometry g).injective,
      realGL_image_openHalfPlane g _ _ hA m hnoA,realGL_image_openHalfPlane g _ _ hB m hnoB,
      realGL_image_openHalfPlane g _ _ hline m hnoC,hout]
    ext u
    simp only [mem_inter_iff]
    tauto
  exact vertical_unitCircle_components_eq_graph _ a b hna hnb hne haC hbC (g • m) hma hmb hEq

/-- The genuine weighted area of an arbitrary normalized ideal triangle, with any finite/ideal status of the other two vertices. -/
theorem ClosedDiscTriangle.normalized_ideal_area (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hpEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) =
      ∞)
    (hline : (g • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier)
    (a b : ℂ) (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a
      : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b
      : OnePoint ℂ))
    (hA : (g • · : ℍ → ℍ) '' T.sideLineA.toHalfPlane.carrier = (HalfPlaneLine.vertical b.re).carrier)
    (hB : (g • · : ℍ → ℍ) '' T.sideLineB.toHalfPlane.carrier = (HalfPlaneLine.vertical a.re).carrier) :
    volume T.halfPlaneInterior = ENNReal.ofReal
      (Real.arcsin (max a.re b.re) - Real.arcsin (min a.re b.re)) := by
  have he := T.normalized_interior_eq_graph hc g hg hpEnd hline a b hna hnb hne ha hb hA hB
  have hv := measure_smul (volume : Measure ℍ) g T.halfPlaneInterior
  change volume ((g • · : ℍ → ℍ) '' T.halfPlaneInterior) = volume T.halfPlaneInterior at hv
  rw [← hv,he]
  have har : |a.re| ≤ 1 := by simpa only [hna] using Complex.abs_re_le_norm a
  have hbr : |b.re| ≤ 1 := by simpa only [hnb] using Complex.abs_re_le_norm b
  exact halfPlaneAboveUnitCircle_volume_closed (le_min (abs_le.mp har).1 (abs_le.mp hbr).1)
    min_le_max (max_le (abs_le.mp har).2 (abs_le.mp hbr).2)

/-- Every actual triangle with an ideal third vertex has such an evaluated density area; normalization is constructed rather than assumed. -/
theorem ClosedDiscTriangle.exists_ideal_area_coordinates (T : ClosedDiscTriangle)
    (hc : ‖(T.c : ℂ)‖ = 1) :
    ∃ (g : GL (Fin 2) ℝ) (a b : ℂ), 0 < g.val.det ∧ ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      0 ≤ a.im ∧ 0 ≤ b.im ∧ a.re ≠ b.re ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.c)) = ∞ ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.a)) = (a :
        OnePoint ℂ) ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) (extendedCayley.symm (closedDiscToExtended T.b)) = (b :
        OnePoint ℂ) ∧
      volume T.halfPlaneInterior = ENNReal.ofReal
        (Real.arcsin (max a.re b.re) - Real.arcsin (min a.re b.re)) := by
  obtain ⟨g,hg,hpEnd,hline⟩ := T.exists_ideal_vertex_area_normalizer hc
  obtain ⟨a,b,hna,hnb,hia,hib,hne,ha,hb,hA,hB⟩ := T.normalized_sides_and_vertices hc g hg hpEnd hline
  exact ⟨g,a,b,hg,hna,hnb,hia,hib,hne,hpEnd,ha,hb,
    T.normalized_ideal_area hc g hg hpEnd hline a b hna hnb hne ha hb hA hB⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
