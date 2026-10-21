/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
open Set MeasureTheory InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The ordinary half-plane has exactly its genuine extended finite trace. -/
theorem extendedHalfPlanePoint_image_univ :
    extendedHalfPlanePoint '' (univ : Set ℍ) = openHalfPlaneSet := by
  apply subset_antisymm
  · rintro _ ⟨z,_,rfl⟩
    exact (coe_mem_openHalfPlaneSet (z : ℂ)).mpr z.im_pos
  · rintro p ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,mem_univ _,rfl⟩

/-- The actual extended fractional-linear map preserves the whole closed model. -/
theorem realGL_image_closedHalfPlaneSet (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' closedHalfPlaneSet = closedHalfPlaneSet := by
  have hi : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' openHalfPlaneSet = openHalfPlaneSet := by
    have he := realGL_extended_image g hg univ
    have him : (g • · : ℍ → ℍ) '' univ = univ := by
      rw [image_univ]
      exact range_eq_univ.mpr (Homeomorph.smul g : ℍ ≃ₜ ℍ).surjective
    rw [him,extendedHalfPlanePoint_image_univ] at he
    exact he.symm
  rw [← closure_openHalfPlaneSet]
  change (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix
    g)) '' closure openHalfPlaneSet = closure openHalfPlaneSet
  rw [(Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).image_closure]
  exact congrArg closure hi

/-- A determinant-positive real fractional-linear isometry acts on the actual compactified half-plane. -/
def realGLClosedHalfPlaneHomeomorph (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    ClosedHalfPlaneModel ≃ₜ ClosedHalfPlaneModel :=
  (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).subtype (fun p => by
    conv_rhs => rw [← realGL_image_closedHalfPlaneSet g hg]
    exact (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)).injective.mem_set_image.symm)

theorem realGLClosedHalfPlaneHomeomorph_finite (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    realGLClosedHalfPlaneHomeomorph g hg (halfPlaneToClosedModel z) = halfPlaneToClosedModel (g • z) := by
  apply Subtype.ext
  exact realMobiusMatrix_coe g hg z

/-- The actual reflected real-linear plane homeomorphism extends through infinity. -/
def axisReflectionExtendedHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  (Complex.conjCLE.toHomeomorph.trans (Homeomorph.neg ℂ)).onePointCongr

theorem axisReflectionExtendedHomeomorph_closed (p : OnePoint ℂ) :
    p ∈ closedHalfPlaneSet ↔ axisReflectionExtendedHomeomorph p ∈ closedHalfPlaneSet := by
  cases p with
  | infty => simp [axisReflectionExtendedHomeomorph,closedHalfPlaneSet]
  | coe z =>
    change (z : OnePoint ℂ) ∈ closedHalfPlaneSet ↔ ((-conj z : ℂ) : OnePoint ℂ) ∈ closedHalfPlaneSet
    simp only [coe_mem_closedHalfPlaneSet,Complex.neg_im,Complex.conj_im,neg_neg]

/-- Reflection is a genuine homeomorphism of the actual closed model. -/
def axisReflectionClosedHalfPlaneHomeomorph : ClosedHalfPlaneModel ≃ₜ ClosedHalfPlaneModel :=
  axisReflectionExtendedHomeomorph.subtype axisReflectionExtendedHomeomorph_closed

theorem axisReflectionClosedHalfPlaneHomeomorph_finite (z : ℍ) :
    axisReflectionClosedHalfPlaneHomeomorph (halfPlaneToClosedModel z) =
      halfPlaneToClosedModel (UpperHalfPlane.J • z) := by
  apply Subtype.ext
  change ((-conj (z : ℂ) : ℂ) : OnePoint ℂ) = (((UpperHalfPlane.J • z : ℍ) : ℂ) : OnePoint ℂ)
  rw [UpperHalfPlane.coe_J_smul]

/-- Every actual hyperbolic isometry has an actual homeomorphic extension to all finite and ideal points. -/
theorem isometry_exists_closedHalfPlaneHomeomorph {f : ℍ → ℍ} (hf : Isometry f) :
    ∃ e : ClosedHalfPlaneModel ≃ₜ ClosedHalfPlaneModel,
      ∀ z : ℍ,e (halfPlaneToClosedModel z) = halfPlaneToClosedModel (f z) := by
  obtain ⟨s,hs⟩ := isometry_exists_sl2_or_reflected hf
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by simp [g]
  rcases hs with hs | hs
  · refine ⟨realGLClosedHalfPlaneHomeomorph g hg,?_⟩
    intro z
    rw [realGLClosedHalfPlaneHomeomorph_finite,hs]
    rfl
  · refine ⟨axisReflectionClosedHalfPlaneHomeomorph.trans (realGLClosedHalfPlaneHomeomorph g hg),?_⟩
    intro z
    change realGLClosedHalfPlaneHomeomorph g hg (axisReflectionClosedHalfPlaneHomeomorph (halfPlaneToClosedModel z)) = _
    rw [axisReflectionClosedHalfPlaneHomeomorph_finite,realGLClosedHalfPlaneHomeomorph_finite,hs]
    rfl

/-- Every actual native disc isometry extends to the actual Euclidean closed-disc compactification. -/
theorem discPathIsometry_exists_closedHomeomorph (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) :
    ∃ e : 𝕔𝔻 ≃ₜ 𝕔𝔻,∀ z : 𝔻,e (discToClosedModel z) = discToClosedModel (f z) := by
  obtain ⟨e,he⟩ := isometry_exists_closedHalfPlaneHomeomorph (discPathIsometry_conjugate hf)
  refine ⟨closedModelCayleyHomeomorph.symm.trans (e.trans closedModelCayleyHomeomorph),?_⟩
  intro z
  change closedModelCayleyHomeomorph (e (closedModelCayleyHomeomorph.symm (discToClosedModel z))) = _
  have hz : closedModelCayleyHomeomorph.symm (discToClosedModel z) = halfPlaneToClosedModel (discToHalfPlane z) := by
    apply closedModelCayleyHomeomorph.injective
    rw [closedModelCayleyHomeomorph.apply_symm_apply,closedModelCayley_on_interior,halfPlaneToDisc_discToHalfPlane]
  rw [hz,he,closedModelCayley_on_interior]
  simp only [halfPlaneToDisc_discToHalfPlane]

/-- A genuine closed-model isometry, with its distance-preserving finite restriction. -/
structure ClosedDiscIsometry where
  finiteMap : 𝔻 → 𝔻
  distance_eq : ∀ z w,discPathDist (finiteMap z) (finiteMap w) = discPathDist z w
  closedMap : 𝕔𝔻 ≃ₜ 𝕔𝔻
  finite_commutes : ∀ z,closedMap (discToClosedModel z) = discToClosedModel (finiteMap z)

/-- No extension hypothesis is required of a caller's actual distance-preserving map. -/
def ClosedDiscIsometry.ofPathIsometry (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) : ClosedDiscIsometry where
  finiteMap := f
  distance_eq := hf
  closedMap := (discPathIsometry_exists_closedHomeomorph f hf).choose
  finite_commutes := (discPathIsometry_exists_closedHomeomorph f hf).choose_spec

theorem ClosedDiscIsometry.finiteMap_bijective (e : ClosedDiscIsometry) : Function.Bijective e.finiteMap := by
  constructor
  · intro z w he
    have hc : discToClosedModel z = discToClosedModel w := e.closedMap.injective (by rw [e.finite_commutes,e.finite_commutes,he])
    exact Complex.UnitDisc.coe_injective (congrArg (fun p : 𝕔𝔻 => (p : ℂ)) hc)
  · obtain ⟨g,hg⟩ := isometry_exists_realGL (discPathIsometry_conjugate e.distance_eq)
    intro z
    refine ⟨halfPlaneToDisc (g⁻¹ • discToHalfPlane z),?_⟩
    apply discToHalfPlane_injective
    have he := congrFun hg (g⁻¹ • discToHalfPlane z)
    simpa only [smul_inv_smul] using he

def ClosedDiscIsometry.finiteEquiv (e : ClosedDiscIsometry) : 𝔻 ≃ 𝔻 :=
  Equiv.ofBijective e.finiteMap e.finiteMap_bijective

/-- The inverse preserves the same actual metric and compactification. -/
def ClosedDiscIsometry.symm (e : ClosedDiscIsometry) : ClosedDiscIsometry where
  finiteMap := e.finiteEquiv.symm
  distance_eq z w := by
    have he := e.distance_eq (e.finiteEquiv.symm z) (e.finiteEquiv.symm w)
    change discPathDist (e.finiteEquiv (e.finiteEquiv.symm z)) (e.finiteEquiv (e.finiteEquiv.symm w)) = _ at he
    rw [e.finiteEquiv.apply_symm_apply,e.finiteEquiv.apply_symm_apply] at he
    exact he.symm
  closedMap := e.closedMap.symm
  finite_commutes z := by
    apply e.closedMap.injective
    rw [e.closedMap.apply_symm_apply,e.finite_commutes]
    change discToClosedModel z = discToClosedModel (e.finiteEquiv (e.finiteEquiv.symm z))
    rw [e.finiteEquiv.apply_symm_apply]

/-- Genuine finite h-lines have their actual h-line images under any native isometry. -/
theorem discPathIsometry_image_discLine (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) (L : DiscLine) :
    ∃ M : DiscLine,f '' L.carrier = M.carrier := by
  obtain ⟨g,hg⟩ := isometry_exists_realGL (discPathIsometry_conjugate hf)
  obtain ⟨N,hN⟩ := realGL_image_hLine g L.toHalfPlane
  refine ⟨N.toDiscLine,?_⟩
  have him : f '' L.carrier = halfPlaneToDisc '' ((g • · : ℍ → ℍ) '' L.toHalfPlane.carrier) := by
    rw [L.carrier_eq_cayley_image_halfPlane,image_image,image_image]
    apply image_congr
    intro z _
    apply discToHalfPlane_injective
    have he := congrFun hg z
    simpa only [discToHalfPlane_halfPlaneToDisc] using he
  rw [him,hN,N.toDiscLine_carrier,N.discCarrier_eq_cayley_image]

/-- Images of actual finite traces commute with the actual closed-model embedding. -/
theorem ClosedDiscIsometry.closedMap_image_finite (e : ClosedDiscIsometry) (S : Set 𝔻) :
    e.closedMap '' (discToClosedModel '' S) = discToClosedModel '' (e.finiteMap '' S) := by
  rw [image_image,image_image]
  apply image_congr
  intro z _
  exact e.finite_commutes z

/-- The homeomorphic extension maps the actual entire closed h-line, including its ideal ends. -/
theorem ClosedDiscIsometry.image_closedLine (e : ClosedDiscIsometry) (L : DiscLine) :
    ∃ M : DiscLine,e.closedMap '' L.closedCarrier = M.closedCarrier := by
  obtain ⟨M,hM⟩ := discPathIsometry_image_discLine e.finiteMap e.distance_eq L
  refine ⟨M,?_⟩
  rw [DiscLine.closedCarrier,e.closedMap.image_closure,e.closedMap_image_finite,hM]
  rfl

/-- The genuine image of a finite-or-ideal triangle under an arbitrary closed-model isometry. -/
def ClosedDiscTriangle.mapClosedIsometry (T : ClosedDiscTriangle) (e : ClosedDiscIsometry) : ClosedDiscTriangle where
  a := e.closedMap T.a
  b := e.closedMap T.b
  c := e.closedMap T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    obtain ⟨M,hM⟩ := e.symm.image_closedLine L
    apply T.noncollinear
    refine ⟨M,?_,?_,?_⟩
    · rw [← hM]
      exact ⟨e.closedMap T.a,ha,e.closedMap.symm_apply_apply _⟩
    · rw [← hM]
      exact ⟨e.closedMap T.b,hb,e.closedMap.symm_apply_apply _⟩
    · rw [← hM]
      exact ⟨e.closedMap T.c,hc,e.closedMap.symm_apply_apply _⟩

/-- Actual finite status is preserved in both directions. -/
theorem ClosedDiscIsometry.finite_iff (e : ClosedDiscIsometry) (p : 𝕔𝔻) :
    ‖(e.closedMap p : ℂ)‖ < 1 ↔ ‖(p : ℂ)‖ < 1 := by
  constructor
  · intro hp
    let z := closedDiscFinitePoint (e.closedMap p) hp
    obtain ⟨w,hw⟩ := e.finiteMap_bijective.2 z
    have he : p = discToClosedModel w := e.closedMap.injective (by
      rw [e.finite_commutes,hw]
      exact (closedDiscFinitePoint_spec (e.closedMap p) hp).symm)
    rw [he]
    exact w.norm_lt_one
  · intro hp
    let z := closedDiscFinitePoint p hp
    have he := e.finite_commutes z
    rw [closedDiscFinitePoint_spec p hp] at he
    rw [he]
    exact (e.finiteMap z).norm_lt_one

/-- Actual ideal status is preserved, including every ideal end. -/
theorem ClosedDiscIsometry.ideal_iff (e : ClosedDiscIsometry) (p : 𝕔𝔻) :
    ‖(e.closedMap p : ℂ)‖ = 1 ↔ ‖(p : ℂ)‖ = 1 := by
  constructor
  · intro hp
    apply le_antisymm p.norm_le_one
    by_contra! hn
    have he := (e.finite_iff p).mpr hn
    rw [hp] at he
    exact (lt_irrefl (1 : ℝ)) he
  · intro hp
    apply le_antisymm (e.closedMap p).norm_le_one
    by_contra! hn
    have he := (e.finite_iff p).mp hn
    rw [hp] at he
    exact (lt_irrefl (1 : ℝ)) he

/-- Genuine finite distances and the source infinite-side convention are preserved together. -/
theorem ClosedDiscIsometry.extendedSideLength_eq (e : ClosedDiscIsometry) (p q : 𝕔𝔻) :
    extendedDiscSideLength (e.closedMap p) (e.closedMap q) = extendedDiscSideLength p q := by
  rcases closedDisc_interior_or_ideal p with ⟨z,hz⟩ | hp
  · rcases closedDisc_interior_or_ideal q with ⟨w,hw⟩ | hq
    · rw [← hz,← hw,e.finite_commutes,e.finite_commutes,
        extendedDiscSideLength_finite,extendedDiscSideLength_finite,e.distance_eq]
    · rw [extendedDiscSideLength_ideal_right _ _ ((e.ideal_iff q).mpr hq),
        extendedDiscSideLength_ideal_right _ _ hq]
  · rw [extendedDiscSideLength_ideal_left _ _ ((e.ideal_iff p).mpr hp),
      extendedDiscSideLength_ideal_left _ _ hp]

theorem ClosedDiscTriangle.mapClosedIsometry_lengths (T : ClosedDiscTriangle) (e : ClosedDiscIsometry) :
    (T.mapClosedIsometry e).lengthA = T.lengthA ∧
      (T.mapClosedIsometry e).lengthB = T.lengthB ∧ (T.mapClosedIsometry e).lengthC = T.lengthC := by
  exact ⟨e.extendedSideLength_eq T.b T.c,e.extendedSideLength_eq T.c T.a,e.extendedSideLength_eq T.a T.b⟩

/-- The actual conjugate finite trace has the expected ordinary image. -/
theorem discPathIsometry_conjugate_image (f : 𝔻 → 𝔻) (S : Set 𝔻) :
    (fun z : ℍ => discToHalfPlane (f (halfPlaneToDisc z))) '' (discToHalfPlane '' S) =
      discToHalfPlane '' (f '' S) := by
  rw [image_image,image_image]
  apply image_congr
  intro z _
  rw [halfPlaneToDisc_discToHalfPlane]

/-- The actual image of a native ray is again a genuine ray. -/
def DiscRayAt.mapClosedIsometry {z : 𝔻} (R : DiscRayAt z) (e : ClosedDiscIsometry) : DiscRayAt (e.finiteMap z) := by
  let F : ℍ → ℍ := fun u => discToHalfPlane (e.finiteMap (halfPlaneToDisc u))
  let S := R.toHalfPlane.mapIsometry F (discPathIsometry_conjugate e.distance_eq)
  let a := S.idealEndpoint
  have hS : IsHLineRay (discToHalfPlane (e.finiteMap z)) a (discToHalfPlane '' (e.finiteMap '' R.val)) := by
    have he : IsHLineRay (F (discToHalfPlane z)) a S.val := S.isRay
    rw [← R.toHalfPlane.mapIsometry_carrier F (discPathIsometry_conjugate e.distance_eq)] at he
    change IsHLineRay (F (discToHalfPlane z)) a (F '' (discToHalfPlane '' R.val)) at he
    rw [discPathIsometry_conjugate_image] at he
    simpa only [F,halfPlaneToDisc_discToHalfPlane] using he
  refine ⟨e.finiteMap '' R.val,extendedCayley a,(idealBoundary_cayley_iff a).mp S.idealEndpoint_mem,?_⟩
  have hd := hS.toDisc
  rwa [halfPlaneToDisc_discToHalfPlane,cayley_image_inverse_image] at hd

theorem DiscRayAt.mapClosedIsometry_carrier {z : 𝔻} (R : DiscRayAt z) (e : ClosedDiscIsometry) :
    (R.mapClosedIsometry e).val = e.finiteMap '' R.val := rfl

/-- Ray-angle measurements are insensitive to a proved change of the displayed common base point. -/
theorem hInteriorAngleMeasure_congr_base {z w : ℍ} (hzw : z = w)
    (R S : HRayAt z) (R' S' : HRayAt w) (hR : R.val = R'.val) (hS : S.val = S'.val) :
    hInteriorAngleMeasure R S = hInteriorAngleMeasure R' S' := by
  subst w
  rw [Subtype.ext hR,Subtype.ext hS]

/-- The genuine forward-ray angle is preserved for every actual native isometry. -/
theorem discInteriorAngleMeasure_mapClosedIsometry {z : 𝔻} (R S : DiscRayAt z) (e : ClosedDiscIsometry) :
    discInteriorAngleMeasure (R.mapClosedIsometry e) (S.mapClosedIsometry e) = discInteriorAngleMeasure R S := by
  let F : ℍ → ℍ := fun u => discToHalfPlane (e.finiteMap (halfPlaneToDisc u))
  have hF := discPathIsometry_conjugate e.distance_eq
  have hb : F (discToHalfPlane z) = discToHalfPlane (e.finiteMap z) := by simp only [F,halfPlaneToDisc_discToHalfPlane]
  have hR : (R.toHalfPlane.mapIsometry F hF).val = (R.mapClosedIsometry e).toHalfPlane.val := by
    rw [← R.toHalfPlane.mapIsometry_carrier]
    exact discPathIsometry_conjugate_image e.finiteMap R.val
  have hS : (S.toHalfPlane.mapIsometry F hF).val = (S.mapClosedIsometry e).toHalfPlane.val := by
    rw [← S.toHalfPlane.mapIsometry_carrier]
    exact discPathIsometry_conjugate_image e.finiteMap S.val
  rw [discInteriorAngleMeasure_eq_halfPlane,discInteriorAngleMeasure_eq_halfPlane]
  rw [← hInteriorAngleMeasure_congr_base hb _ _ _ _ hR hS,hInteriorAngleMeasure_mapIsometry]

/-- The true ideal endpoint is an actual closure point in the native compactification. -/
theorem DiscRayAt.ideal_mem_closedClosure {z : 𝔻} (R : DiscRayAt z) (w : 𝕔𝔻)
    (hE : R.idealEndpoint = closedDiscToExtended w) : w ∈ discClosedModelClosure R.val := by
  apply isEmbedding_closedDiscToExtended.injective.mem_set_image.mp
  rw [discClosedModelClosure_ambient]
  have he : R.idealEndpoint ∈ discTraceIdealEndpoints R.val := by
    rw [R.trace_idealEndpoint]
    exact mem_singleton _
  rw [hE] at he
  exact he.1

/-- The actual compactified endpoint of an image ray is the image of the original endpoint. -/
theorem DiscRayAt.mapClosedIsometry_idealEndpoint {z : 𝔻} (R : DiscRayAt z) (e : ClosedDiscIsometry)
    (w : 𝕔𝔻) (hw : ‖(w : ℂ)‖ = 1) (hE : R.idealEndpoint = closedDiscToExtended w) :
    (R.mapClosedIsometry e).idealEndpoint = closedDiscToExtended (e.closedMap w) := by
  have hcl := mem_image_of_mem e.closedMap (R.ideal_mem_closedClosure w hE)
  change e.closedMap w ∈ e.closedMap '' closure (discToClosedModel '' R.val) at hcl
  rw [e.closedMap.image_closure,e.closedMap_image_finite] at hcl
  have he := mem_image_of_mem closedDiscToExtended hcl
  change closedDiscToExtended (e.closedMap w) ∈
    closedDiscToExtended '' discClosedModelClosure (e.finiteMap '' R.val) at he
  rw [discClosedModelClosure_ambient] at he
  have htrace : closedDiscToExtended (e.closedMap w) ∈ discTraceIdealEndpoints (R.mapClosedIsometry e).val :=
    ⟨he,(coe_mem_extendedDiscIdealBoundary _).mpr ((e.ideal_iff w).mpr hw)⟩
  rw [(R.mapClosedIsometry e).trace_idealEndpoint] at htrace
  exact (mem_singleton_iff.mp htrace).symm

/-- A genuine first corner ray maps to the corresponding genuine corner ray, including an ideal second vertex. -/
theorem ClosedDiscTriangle.mapClosedIsometry_cornerAB (T : ClosedDiscTriangle) (e : ClosedDiscIsometry)
    (z : 𝔻) (ha : T.a = discToClosedModel z) :
    (T.mapClosedIsometry e).cornerRayABAtA (e.finiteMap z)
      (by change e.closedMap T.a = _; rw [ha,e.finite_commutes]) =
      (T.cornerRayABAtA z ha).mapClosedIsometry e := by
  let U := T.mapClosedIsometry e
  have haU : U.a = discToClosedModel (e.finiteMap z) := by change e.closedMap T.a = _; rw [ha,e.finite_commutes]
  change U.cornerRayABAtA (e.finiteMap z) haU = _
  rcases closedDisc_interior_or_ideal T.b with ⟨w,hw⟩ | hb
  · have hbU : U.b = discToClosedModel (e.finiteMap w) := by change e.closedMap T.b = _; rw [← hw,e.finite_commutes]
    have hzw : z ≠ w := by intro he; exact T.a_ne_b (ha.trans ((congrArg discToClosedModel he).trans hw))
    have hR : w ∈ (T.cornerRayABAtA z ha).val := by
      rw [T.cornerAB_eq_through_finite z w ha hw.symm hzw]
      exact discRayThrough_mem z w hzw
    have hn : e.finiteMap z ≠ e.finiteMap w := e.finiteMap_bijective.1.ne hzw
    rw [U.cornerAB_eq_through_finite _ _ haU hbU hn]
    apply discRayThrough_eq hn
    exact ⟨w,hR,rfl⟩
  · apply DiscRayAt.eq_of_idealEndpoint_eq
    rw [U.cornerRayABAtA_idealEndpoint _ haU ((e.ideal_iff T.b).mpr hb),
      DiscRayAt.mapClosedIsometry_idealEndpoint _ e T.b hb (T.cornerRayABAtA_idealEndpoint z ha hb)]
    rfl

/-- The other genuine first corner ray has the same compatibility for a finite or ideal third vertex. -/
theorem ClosedDiscTriangle.mapClosedIsometry_cornerAC (T : ClosedDiscTriangle) (e : ClosedDiscIsometry)
    (z : 𝔻) (ha : T.a = discToClosedModel z) :
    (T.mapClosedIsometry e).cornerRayACAtA (e.finiteMap z)
      (by change e.closedMap T.a = _; rw [ha,e.finite_commutes]) =
      (T.cornerRayACAtA z ha).mapClosedIsometry e := by
  let U := T.mapClosedIsometry e
  have haU : U.a = discToClosedModel (e.finiteMap z) := by change e.closedMap T.a = _; rw [ha,e.finite_commutes]
  change U.cornerRayACAtA (e.finiteMap z) haU = _
  rcases closedDisc_interior_or_ideal T.c with ⟨w,hw⟩ | hc
  · have hcU : U.c = discToClosedModel (e.finiteMap w) := by change e.closedMap T.c = _; rw [← hw,e.finite_commutes]
    have hzw : z ≠ w := by intro he; exact T.c_ne_a ((ha.trans ((congrArg discToClosedModel he).trans hw)).symm)
    have hR : w ∈ (T.cornerRayACAtA z ha).val := by
      rw [T.cornerAC_eq_through_finite z w ha hw.symm hzw]
      exact discRayThrough_mem z w hzw
    have hn : e.finiteMap z ≠ e.finiteMap w := e.finiteMap_bijective.1.ne hzw
    rw [U.cornerAC_eq_through_finite _ _ haU hcU hn]
    apply discRayThrough_eq hn
    exact ⟨w,hR,rfl⟩
  · apply DiscRayAt.eq_of_idealEndpoint_eq
    rw [U.cornerRayACAtA_idealEndpoint _ haU ((e.ideal_iff T.c).mpr hc),
      DiscRayAt.mapClosedIsometry_idealEndpoint _ e T.c hc (T.cornerRayACAtA_idealEndpoint z ha hc)]
    rfl

/-- Every actual finite or ideal first angle is preserved. -/
theorem ClosedDiscTriangle.mapClosedIsometry_alpha (T : ClosedDiscTriangle) (e : ClosedDiscIsometry) :
    (T.mapClosedIsometry e).alpha = T.alpha := by
  rcases closedDisc_interior_or_ideal T.a with ⟨z,hz⟩ | ha
  · have hmap : (T.mapClosedIsometry e).a = discToClosedModel (e.finiteMap z) := by
      change e.closedMap T.a = _
      rw [← hz,e.finite_commutes]
    rw [(T.mapClosedIsometry e).alpha_of_finite _ hmap,T.alpha_of_finite z hz.symm,
      T.mapClosedIsometry_cornerAB e z hz.symm,T.mapClosedIsometry_cornerAC e z hz.symm,
      discInteriorAngleMeasure_mapClosedIsometry]
  · rw [(T.mapClosedIsometry e).alpha_of_ideal ((e.ideal_iff T.a).mpr ha),T.alpha_of_ideal ha]

/-- All three actual corner angles, including the source zero-angle convention at ideal vertices, are preserved. -/
theorem ClosedDiscTriangle.mapClosedIsometry_angles (T : ClosedDiscTriangle) (e : ClosedDiscIsometry) :
    (T.mapClosedIsometry e).alpha = T.alpha ∧ (T.mapClosedIsometry e).beta = T.beta ∧
      (T.mapClosedIsometry e).gamma = T.gamma :=
  ⟨T.mapClosedIsometry_alpha e,T.cycle.mapClosedIsometry_alpha e,T.cycle.cycle.mapClosedIsometry_alpha e⟩

/-- The actual image triangle is defined for any native distance-preserving map, with no onto or boundary-extension assumption. -/
def ClosedDiscTriangle.mapPathIsometry (T : ClosedDiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) : ClosedDiscTriangle :=
  T.mapClosedIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry f hf)

theorem ClosedDiscTriangle.mapPathIsometry_lengths (T : ClosedDiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) :
    (T.mapPathIsometry f hf).lengthA = T.lengthA ∧ (T.mapPathIsometry f hf).lengthB = T.lengthB ∧
      (T.mapPathIsometry f hf).lengthC = T.lengthC := T.mapClosedIsometry_lengths _

theorem ClosedDiscTriangle.mapPathIsometry_angles (T : ClosedDiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) :
    (T.mapPathIsometry f hf).alpha = T.alpha ∧ (T.mapPathIsometry f hf).beta = T.beta ∧
      (T.mapPathIsometry f hf).gamma = T.gamma := T.mapClosedIsometry_angles _

/-- The displayed image vertices come from a genuine homeomorphism extending the original map. -/
theorem ClosedDiscTriangle.mapPathIsometry_witness (T : ClosedDiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) :
    ∃ e : 𝕔𝔻 ≃ₜ 𝕔𝔻,(∀ z : 𝔻,e (discToClosedModel z) = discToClosedModel (f z)) ∧
      (T.mapPathIsometry f hf).a = e T.a ∧ (T.mapPathIsometry f hf).b = e T.b ∧
      (T.mapPathIsometry f hf).c = e T.c :=
  ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry f hf).closedMap,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry f
      hf).finite_commutes,rfl,rfl,rfl⟩

/-- Genuine compactified native triangles can also be transported back through Cayley. -/
def ClosedDiscTriangle.toHalfPlane (T : ClosedDiscTriangle) : ClosedHTriangle where
  a := closedModelCayleyHomeomorph.symm T.a
  b := closedModelCayleyHomeomorph.symm T.b
  c := closedModelCayleyHomeomorph.symm T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    apply T.noncollinear
    refine ⟨L.toDiscLine,?_,?_,?_⟩
    · rw [← L.cayley_image_closedCarrier]
      exact ⟨closedModelCayleyHomeomorph.symm T.a,ha,closedModelCayleyHomeomorph.apply_symm_apply _⟩
    · rw [← L.cayley_image_closedCarrier]
      exact ⟨closedModelCayleyHomeomorph.symm T.b,hb,closedModelCayleyHomeomorph.apply_symm_apply _⟩
    · rw [← L.cayley_image_closedCarrier]
      exact ⟨closedModelCayleyHomeomorph.symm T.c,hc,closedModelCayleyHomeomorph.apply_symm_apply _⟩

theorem ClosedDiscTriangle.toHalfPlane_toDiscTriangle (T : ClosedDiscTriangle) :
    T.toHalfPlane.toDiscTriangle = T := by
  cases T
  simp only [ClosedDiscTriangle.toHalfPlane,ClosedHTriangle.toDiscTriangle,Homeomorph.apply_symm_apply]

theorem ClosedHTriangle.toDiscTriangle_toHalfPlane (T : ClosedHTriangle) :
    T.toDiscTriangle.toHalfPlane = T := by
  cases T
  simp only [ClosedDiscTriangle.toHalfPlane,ClosedHTriangle.toDiscTriangle,Homeomorph.symm_apply_apply]

/-- The actual half-plane isometry induces the actual native disc path isometry. -/
theorem halfPlaneIsometry_native_distance {f : ℍ → ℍ} (hf : Isometry f) (z w : 𝔻) :
    discPathDist (halfPlaneToDisc (f (discToHalfPlane z))) (halfPlaneToDisc (f (discToHalfPlane w))) =
      discPathDist z w := by
  rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc,
    hf.dist_eq,discPathDist_eq_halfPlane]

/-- A genuine compactified H triangle is mapped under any actual metric isometry, including all ideal vertices. -/
def ClosedHTriangle.mapIsometry (T : ClosedHTriangle) (f : ℍ → ℍ) (hf : Isometry f) : ClosedHTriangle :=
  (T.toDiscTriangle.mapPathIsometry (fun z => halfPlaneToDisc (f (discToHalfPlane z)))
    (halfPlaneIsometry_native_distance hf)).toHalfPlane

theorem ClosedHTriangle.mapIsometry_lengths (T : ClosedHTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    (T.mapIsometry f hf).lengthA = T.lengthA ∧ (T.mapIsometry f hf).lengthB = T.lengthB ∧
      (T.mapIsometry f hf).lengthC = T.lengthC := by
  change ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).lengthA = T.lengthA ∧
    ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).lengthB = T.lengthB ∧
    ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).lengthC = T.lengthC
  rw [ClosedDiscTriangle.toHalfPlane_toDiscTriangle]
  exact T.toDiscTriangle.mapPathIsometry_lengths _ _

theorem ClosedHTriangle.mapIsometry_angles (T : ClosedHTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    (T.mapIsometry f hf).alpha = T.alpha ∧ (T.mapIsometry f hf).beta = T.beta ∧
      (T.mapIsometry f hf).gamma = T.gamma := by
  change ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).alpha = T.alpha ∧
    ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).beta = T.beta ∧
    ((T.toDiscTriangle.mapPathIsometry _ _).toHalfPlane.toDiscTriangle).gamma = T.gamma
  rw [ClosedDiscTriangle.toHalfPlane_toDiscTriangle]
  exact T.toDiscTriangle.mapPathIsometry_angles _ _

theorem closedModelCayley_inverse_finite (z : 𝔻) :
    closedModelCayleyHomeomorph.symm (discToClosedModel z) = halfPlaneToClosedModel (discToHalfPlane z) := by
  apply closedModelCayleyHomeomorph.injective
  rw [closedModelCayleyHomeomorph.apply_symm_apply,closedModelCayley_on_interior,halfPlaneToDisc_discToHalfPlane]

/-- The H image vertices belong to a true compactified extension of precisely the caller's isometry. -/
theorem ClosedHTriangle.mapIsometry_witness (T : ClosedHTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    ∃ e : ClosedHalfPlaneModel ≃ₜ ClosedHalfPlaneModel,
      (∀ z : ℍ,e (halfPlaneToClosedModel z) = halfPlaneToClosedModel (f z)) ∧
      (T.mapIsometry f hf).a = e T.a ∧ (T.mapIsometry f hf).b = e T.b ∧ (T.mapIsometry f hf).c = e T.c := by
  let F : 𝔻 → 𝔻 := fun z => halfPlaneToDisc (f (discToHalfPlane z))
  let E := _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry F (halfPlaneIsometry_native_distance hf)
  refine ⟨closedModelCayleyHomeomorph.trans (E.closedMap.trans closedModelCayleyHomeomorph.symm),?_,rfl,rfl,rfl⟩
  intro z
  change closedModelCayleyHomeomorph.symm (E.closedMap (closedModelCayleyHomeomorph (halfPlaneToClosedModel z))) = _
  rw [closedModelCayley_on_interior,E.finite_commutes,closedModelCayley_inverse_finite]
  change halfPlaneToClosedModel (discToHalfPlane (halfPlaneToDisc (f (discToHalfPlane (halfPlaneToDisc z))))) = _
  rw [discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc]

/-- The actual density area is preserved along with the entire finite/ideal triangle data. -/
theorem ClosedDiscTriangle.mapPathIsometry_area (T : ClosedDiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w,discPathDist (f z) (f w) = discPathDist z w) :
    discHyperbolicArea (T.mapPathIsometry f hf).interior = discHyperbolicArea T.interior := by
  rw [ClosedDiscTriangle.area_eq_angle_defect,T.area_eq_angle_defect,
    (T.mapPathIsometry_angles f hf).1,(T.mapPathIsometry_angles f hf).2.1,(T.mapPathIsometry_angles f hf).2.2]

theorem ClosedHTriangle.mapIsometry_area (T : ClosedHTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    volume (T.mapIsometry f hf).interior = volume T.interior := by
  rw [ClosedHTriangle.area_eq_angle_defect,T.area_eq_angle_defect,
    (T.mapIsometry_angles f hf).1,(T.mapIsometry_angles f hf).2.1,(T.mapIsometry_angles f hf).2.2]

end
end LowDimensionalTopology.Geometry.Hyperbolic
