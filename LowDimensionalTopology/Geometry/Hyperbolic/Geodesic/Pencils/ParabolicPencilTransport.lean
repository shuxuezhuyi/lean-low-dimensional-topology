/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.ParabolicPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicInversiveProducts
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

/-- The actual part of a genuine generalized circle inside the H model. -/
def halfPlaneCircleCarrier (C : Mobius.ComplexGeneralizedCircle) : Set ℍ :=
  {z | ((z : ℂ) : OnePoint ℂ)∈C.val}

theorem halfPlaneCircleCarrier_realGL_image (C : Mobius.ComplexGeneralizedCircle)
    (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) :
    halfPlaneCircleCarrier (C.image (geodesicRealGLMobius g))=
      (g • · : ℍ → ℍ) '' halfPlaneCircleCarrier C := by
  ext z
  constructor
  · rintro ⟨w,hw,he⟩
    have hp:=realMobiusMatrix_coe g hg (g⁻¹ • z)
    rw [smul_inv_smul] at hp
    have he':=(Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).injective (he.trans hp.symm)
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    change (((g⁻¹ • z : ℍ) : ℂ) : OnePoint ℂ)∈C.val
    rwa [←he']
  · rintro ⟨w,hw,rfl⟩
    exact ⟨((w : ℂ) : OnePoint ℂ),hw,realMobiusMatrix_coe g hg w⟩

def chartHorocycle (g : GL (Fin 2) ℝ) (t : ℝ) : Set ℍ :=
  (g • · : ℍ → ℍ) '' horizontalHorocycle t

def chartHorocycleFamily (g : GL (Fin 2) ℝ) : Set (Set ℍ) :=
  {S | ∃t : ℝ,0<t ∧ S=chartHorocycle g t}

/-- A genuine parabolic pencil is defined by its actual common ideal end. -/
def hParabolicPencil (w : OnePoint ℂ) : Set HalfPlaneLine := {L | w∈L.idealEndpoints}

theorem chartHorocycle_eq_actual_circle (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (t : ℝ) :
    chartHorocycle g t=halfPlaneCircleCarrier ((horizontalHorocycleCircle t).image (geodesicRealGLMobius g)) := by
  rw [halfPlaneCircleCarrier_realGL_image _ g hg]
  change (g • · : ℍ → ℍ) '' horizontalHorocycle t=(g • · : ℍ → ℍ) '' halfPlaneCircleCarrier (horizontalHorocycleCircle
    t)
  congr 1
  exact Set.ext (horizontalHorocycle_eq_circleCarrier t)

theorem horizontalHorocycleCircle_tangent_ideal (t : ℝ) (ht : 0<t) :
    (horizontalHorocycleCircle t).val∩halfPlaneIdealBoundary={(∞ : OnePoint ℂ)} := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [horizontalHorocycleCircle,halfPlaneIdealBoundary]
  | coe z =>
    rw [mem_inter_iff,coe_mem_halfPlaneIdealBoundary]
    change (((z : OnePoint ℂ)∈Mobius.complexLine Complex.I t) ∧ z.im=0) ↔ (z : OnePoint ℂ)=∞
    rw [Mobius.complexLine_coe,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp only [Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,OnePoint.coe_ne_infty,iff_false,not_and]
    intro h ht0
    linarith

theorem chartHorocycleCircle_tangent_ideal (g : GL (Fin 2) ℝ) (t : ℝ) (ht : 0<t) :
    ((horizontalHorocycleCircle t).image (geodesicRealGLMobius g)).val∩halfPlaneIdealBoundary=
      {Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞} := by
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' (horizontalHorocycleCircle
    t).val)∩halfPlaneIdealBoundary=_
  rw [←image_inter_preimage,realMobiusMatrix_preimage_boundary,horizontalHorocycleCircle_tangent_ideal t ht,
    image_singleton]

theorem mem_hParabolicPencil_chart_iff (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (L : HalfPlaneLine) :
    L∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞) ↔
      ∃x : ℝ,L=(HalfPlaneLine.vertical x).realGLMap g := by
  constructor
  · intro hL
    have hinv : (L.realGLMap g⁻¹)∈parabolicPencilAtInfinity := by
      change (∞ : OnePoint ℂ)∈(L.realGLMap g⁻¹).idealEndpoints
      have he:=L.realGLMap_mem_idealEndpoints g⁻¹ (gl_pos_inverse g hg)
        (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞)
      rw [realMobiusMatrix_inv,Mobius.fractionalLinear_inv_apply] at he
      exact he.mpr hL
    obtain ⟨x,hx⟩:=(mem_parabolicPencilAtInfinity_iff _).mp hinv
    refine ⟨x,?_⟩
    rw [←hx,←inv_inv g]
    exact (L.realGLMap_inv g⁻¹).symm
  · rintro ⟨x,rfl⟩
    exact ((HalfPlaneLine.vertical x).realGLMap_mem_idealEndpoints g hg ∞).mpr
      ((mem_parabolicPencilAtInfinity_iff _).mpr ⟨x,rfl⟩)

/-- P1 for every actual positive real Mobius chart. -/
theorem existsUnique_chartHorocycle_through (g : GL (Fin 2) ℝ) (z : ℍ) :
    ∃!S : Set ℍ,S∈chartHorocycleFamily g ∧ z∈S := by
  let w:=g⁻¹ • z
  refine ⟨chartHorocycle g w.im,⟨⟨w.im,w.im_pos,rfl⟩,w,rfl,smul_inv_smul g z⟩,?_⟩
  rintro S ⟨⟨t,ht,rfl⟩,u,hu,he⟩
  have hue : u=w := by
    have hh:=congrArg (fun v : ℍ => g⁻¹ • v) he
    simpa only [inv_smul_smul] using hh
  change u.im=t at hu
  rw [←hu,hue]

/-- P2 for every genuine ideal end realized by a positive real Mobius chart. -/
theorem existsUnique_hParabolicPencil_chart_through (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (z : ℍ) :
    ∃!L : HalfPlaneLine, L∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞) ∧
      z∈L.carrier := by
  let w:=g⁻¹ • z
  let L:=(HalfPlaneLine.vertical w.re).realGLMap g
  refine ⟨L,⟨(mem_hParabolicPencil_chart_iff g hg _).mpr ⟨w.re,rfl⟩,?_⟩,?_⟩
  · rw [HalfPlaneLine.realGLMap_carrier]
    exact ⟨w,rfl,smul_inv_smul g z⟩
  · rintro M ⟨hM,hz⟩
    obtain ⟨x,rfl⟩:=(mem_hParabolicPencil_chart_iff g hg M).mp hM
    have hx : w.re=x := by
      obtain ⟨u,hu,he⟩:=((HalfPlaneLine.vertical x).realGLMap_carrier g) ▸ hz
      have hh:=congrArg (fun v : ℍ => g⁻¹ • v) he
      have hue : u=w:=by simpa only [inv_smul_smul] using hh
      change u.re=x at hu
      simpa only [hue] using hu
    change (HalfPlaneLine.vertical x).realGLMap g=(HalfPlaneLine.vertical w.re).realGLMap g
    rw [hx]


/-- P3 retains actual Euclidean generalized-circle normal orthogonality after transport. -/
theorem chartHorocycleFamily_orthogonal (g : GL (Fin 2) ℝ) (hg : 0<g.val.det)
    (L : HalfPlaneLine) (hL : L∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞))
    (S : Set ℍ) (hS : S∈chartHorocycleFamily g) :
    ∃C : Mobius.ComplexGeneralizedCircle, S=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  obtain ⟨x,rfl⟩:=(mem_hParabolicPencil_chart_iff g hg L).mp hL
  obtain ⟨t,ht,rfl⟩:=hS
  refine ⟨(horizontalHorocycleCircle t).image (geodesicRealGLMobius g),
    chartHorocycle_eq_actual_circle g hg t,?_⟩
  rw [←(HalfPlaneLine.vertical x).extendedCircle_image_realGL _ g hg
    ((HalfPlaneLine.vertical x).realGLMap_carrier g).symm]
  exact (vertical_horizontalHorocycle_orthogonal x t).image _ _ _

/-- P4 uses the actual image-line reflection, with genuine conjugacy. -/
theorem chartHorocycleFamily_reflection (g : GL (Fin 2) ℝ) (hg : 0<g.val.det)
    (L : HalfPlaneLine) (hL : L∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞))
    (S : Set ℍ) (hS : S∈chartHorocycleFamily g) : L.reflection '' S=S := by
  obtain ⟨x,rfl⟩:=(mem_hParabolicPencil_chart_iff g hg L).mp hL
  obtain ⟨t,ht,rfl⟩:=hS
  change ((HalfPlaneLine.vertical x).realGLMap g).reflection '' ((g • · : ℍ → ℍ) '' horizontalHorocycle t)=_
  calc
    _=(g • · : ℍ → ℍ) '' ((HalfPlaneLine.vertical x).reflection '' horizontalHorocycle t) := by
      rw [image_image,image_image]
      congr 1
      funext z
      have he:=(HalfPlaneLine.vertical x).reflection_realGL_conjugation g (g • z)
      simpa only [inv_smul_smul,Function.comp_apply] using he.symm
    _=chartHorocycle g t := by rw [vertical_reflection_horizontalHorocycle]; rfl

theorem hCurvePairDistances_isometry_image (S T : Set ℍ) (f : ℍ → ℍ) (hf : Isometry f) :
    hCurvePairDistances (f '' S) (f '' T)=hCurvePairDistances S T := by
  ext d
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,_,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨p,hp,q,hq,hf.dist_eq p q⟩
  · rintro ⟨p,hp,q,hq,rfl⟩
    exact ⟨f p,mem_image_of_mem f hp,f q,mem_image_of_mem f hq,(hf.dist_eq p q).symm⟩

theorem hCurveDistance_isometry_image (S T : Set ℍ) (f : ℍ → ℍ) (hf : Isometry f) :
    hCurveDistance (f '' S) (f '' T)=hCurveDistance S T := by
  change sInf (hCurvePairDistances (f '' S) (f '' T))=sInf (hCurvePairDistances S T)
  rw [hCurvePairDistances_isometry_image S T f hf]

/-- P5 realizes the actual infimum between the transported genuine curves. -/
theorem chartHorocycleFamily_equidistance (g : GL (Fin 2) ℝ) (hg : 0<g.val.det)
    (S T : Set ℍ) (hS : S∈chartHorocycleFamily g) (hT : T∈chartHorocycleFamily g) (p : ℍ) (hp : p∈S) :
    ∃q : ℍ,q∈T ∧ dist p q=hCurveDistance S T ∧
      ∃L : HalfPlaneLine,L∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞) ∧
        p∈L.carrier ∧ q∈L.carrier := by
  obtain ⟨t,ht,rfl⟩:=hS
  obtain ⟨u,hu,rfl⟩:=hT
  obtain ⟨z,hz,rfl⟩:=hp
  obtain ⟨w,hw,hd,L,hL,hzL,hwL⟩:=horizontalHorocycle_equidistance t u ht hu z hz
  refine ⟨g • w,⟨w,hw,rfl⟩,?_,L.realGLMap g,?_,
    (L.realGLMap_mem_carrier g z).mpr hzL,(L.realGLMap_mem_carrier g w).mpr hwL⟩
  · change dist (g • z) (g • w)=hCurveDistance ((g • · : ℍ → ℍ) '' horizontalHorocycle t)
      ((g • · : ℍ → ℍ) '' horizontalHorocycle u)
    rw [(realGL_isometry g).dist_eq,hCurveDistance_isometry_image _ _ _ (realGL_isometry g)]
    exact hd
  · exact (L.realGLMap_mem_idealEndpoints g hg ∞).mpr hL

theorem hEquidistantLocus_realGL_image (g : GL (Fin 2) ℝ) (a b : ℍ) :
    HEquidistantLocus (g • a) (g • b)=(g • · : ℍ → ℍ) '' HEquidistantLocus a b := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    change dist (g⁻¹ • z) a=dist (g⁻¹ • z) b
    rw [←(realGL_isometry g).dist_eq (g⁻¹ • z) a,←(realGL_isometry g).dist_eq (g⁻¹ • z) b,
      smul_inv_smul]
    exact hz
  · rintro ⟨w,hw,rfl⟩
    change dist (g • w) (g • a)=dist (g • w) (g • b)
    rw [(realGL_isometry g).dist_eq,(realGL_isometry g).dist_eq]
    exact hw

theorem hPerpendicularBisector_realGLMap_iff (g : GL (Fin 2) ℝ) {a b : ℍ} (hab : a≠b)
    (N : HalfPlaneLine) :
    IsHPerpendicularBisector (N.realGLMap g) (g • a) (g • b) ↔ IsHPerpendicularBisector N a b := by
  have hgab : g • a≠g • b:=(realGL_isometry g).injective.ne hab
  rw [hPerpendicularBisector_iff_carrier hgab,hPerpendicularBisector_iff_carrier hab,
    N.realGLMap_carrier,hEquidistantLocus_realGL_image]
  exact (realGL_isometry g).injective.image_injective.eq_iff


theorem same_chartHorocycle_iff (g : GL (Fin 2) ℝ) (a b : ℍ) :
    (∃S∈chartHorocycleFamily g,a∈S ∧ b∈S) ↔ (g⁻¹ • a).im=(g⁻¹ • b).im := by
  constructor
  · rintro ⟨S,⟨t,ht,rfl⟩,⟨u,hu,hea⟩,v,hv,heb⟩
    have ha:=congrArg (fun z : ℍ => g⁻¹ • z) hea
    have hb:=congrArg (fun z : ℍ => g⁻¹ • z) heb
    simp only [inv_smul_smul] at ha hb
    rw [←ha,←hb]
    exact hu.trans hv.symm
  · intro he
    let t:=(g⁻¹ • a).im
    refine ⟨chartHorocycle g t,⟨t,(g⁻¹ • a).im_pos,rfl⟩,
      ⟨g⁻¹ • a,rfl,smul_inv_smul g a⟩,g⁻¹ • b,?_,smul_inv_smul g b⟩
    exact he.symm

/-- P6 for the actual source perpendicular bisector in every positive real chart. -/
theorem chartParabolicPencil_perpendicularBisector_iff (g : GL (Fin 2) ℝ) (hg : 0<g.val.det)
    {a b : ℍ} (hab : a≠b) {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈hParabolicPencil (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞) ↔
      ∃S∈chartHorocycleFamily g,a∈S ∧ b∈S := by
  have hab' : g⁻¹ • a≠g⁻¹ • b:=(realGL_isometry g⁻¹).injective.ne hab
  have hN' : IsHPerpendicularBisector (N.realGLMap g⁻¹) (g⁻¹ • a) (g⁻¹ • b):=
    (hPerpendicularBisector_realGLMap_iff g⁻¹ hab N).mpr hN
  have he:=parabolicPencilAtInfinity_perpendicularBisector_iff hab' hN'
  rw [same_horizontalHorocycle_iff] at he
  rw [same_chartHorocycle_iff]
  rw [←he]
  change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞∈N.idealEndpoints ↔
    (∞ : OnePoint ℂ)∈(N.realGLMap g⁻¹).idealEndpoints
  have hp:=N.realGLMap_mem_idealEndpoints g⁻¹ (gl_pos_inverse g hg)
    (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞)
  rw [realMobiusMatrix_inv,Mobius.fractionalLinear_inv_apply] at hp
  exact hp.symm

/-- An intrinsic actual horocycle is a nonempty H part of a genuine generalized circle
with precisely its designated ideal point on the actual ideal boundary. -/
def IsHHorocycleAt (w : OnePoint ℂ) (S : Set ℍ) : Prop :=
  ∃C : Mobius.ComplexGeneralizedCircle,C.val∩halfPlaneIdealBoundary={w} ∧ S=halfPlaneCircleCarrier C ∧ S.Nonempty

theorem horizontalHorocycle_isHHorocycleAt (t : ℝ) (ht : 0<t) :
    IsHHorocycleAt ∞ (horizontalHorocycle t) := by
  exact ⟨horizontalHorocycleCircle t,horizontalHorocycleCircle_tangent_ideal t ht,
    Set.ext (horizontalHorocycle_eq_circleCarrier t),metricProbe 0 t ht,rfl⟩

theorem IsHHorocycleAt_infty_iff (S : Set ℍ) : IsHHorocycleAt ∞ S ↔ S∈horizontalHorocycleFamily := by
  constructor
  · rintro ⟨C,hC,rfl,z,hz⟩
    have hinf : (∞ : OnePoint ℂ)∈C.val := by
      have hh : (∞ : OnePoint ℂ)∈C.val∩halfPlaneIdealBoundary:=by rw [hC]; exact mem_singleton _
      exact hh.1
    rcases (Mobius.isComplexGeneralizedCircle_iff C.val).mp C.property with ⟨c,r,hr,hcircle⟩ | ⟨a,t,ha,hline⟩
    · rw [hcircle] at hinf
      exact False.elim ((Mobius.complexCircle_infty c r) hinf)
    · have hare : a.re=0 := by
        by_contra hne
        have hp : (((t/a.re : ℝ) : ℂ) : OnePoint ℂ)∈C.val∩halfPlaneIdealBoundary := by
          refine ⟨?_,?_⟩
          · rw [hline, Mobius.complexLine_coe,
            _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
            simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
            exact div_mul_cancel₀ t hne
          · simp [coe_mem_halfPlaneIdealBoundary]
        rw [hC] at hp
        exact OnePoint.coe_ne_infty _ hp
      have haim : a.im≠0 := by
        intro hi
        apply ha
        apply Complex.ext <;> simp [hare,hi]
      have he (v : ℍ) : v∈halfPlaneCircleCarrier C ↔ v.im=t/a.im := by
        change ((v : ℂ) : OnePoint ℂ)∈C.val ↔ _
        rw [hline, Mobius.complexLine_coe,
          _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates, hare, mul_zero, zero_add,
          eq_div_iff haim]
        rfl
      have hz' :=(he z).mp hz
      refine ⟨t/a.im,by rw [←hz']; exact z.im_pos,?_⟩
      ext v
      exact he v
  · rintro ⟨t,ht,rfl⟩
    exact horizontalHorocycle_isHHorocycleAt t ht


theorem IsHHorocycleAt.realGL_image {w : OnePoint ℂ} {S : Set ℍ} (hS : IsHHorocycleAt w S)
    (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) :
    IsHHorocycleAt (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) w) ((g • · : ℍ → ℍ) '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image (geodesicRealGLMobius g),?_,(halfPlaneCircleCarrier_realGL_image C g hg).symm,
    hne.image (g • ·)⟩
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' C.val)∩halfPlaneIdealBoundary=_
  rw [←image_inter_preimage,realMobiusMatrix_preimage_boundary,hC,image_singleton]

/-- All actual horocycles at the designated ideal end occur in every genuine chart. -/
theorem isHHorocycleAt_chart_iff (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (S : Set ℍ) :
    IsHHorocycleAt (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞) S ↔ S∈chartHorocycleFamily g := by
  constructor
  · intro hS
    have hn:=hS.realGL_image g⁻¹ (gl_pos_inverse g hg)
    rw [realMobiusMatrix_inv,Mobius.fractionalLinear_inv_apply] at hn
    obtain ⟨t,ht,he⟩:=(IsHHorocycleAt_infty_iff _).mp hn
    refine ⟨t,ht,?_⟩
    have hh:=congrArg (fun T : Set ℍ => (g • · : ℍ → ℍ) '' T) he
    rw [image_image] at hh
    change S=(g • · : ℍ → ℍ) '' horizontalHorocycle t
    simpa only [smul_inv_smul,image_id'] using hh
  · rintro ⟨t,ht,rfl⟩
    exact (horizontalHorocycle_isHHorocycleAt t ht).realGL_image g hg

/-- A positive real Mobius chart is constructed for every actual ideal end. -/
theorem exists_hParabolicChart (w : OnePoint ℂ) (hw : w∈halfPlaneIdealBoundary) :
    ∃g : GL (Fin 2) ℝ,0<g.val.det ∧ Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞=w := by
  obtain ⟨s,hs⟩:=halfPlaneIdealBoundary_exists_sl2_to_infty w hw
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0<g.val.det:=by change 0<s.val.det; rw [s.property]; norm_num
  refine ⟨g⁻¹,gl_pos_inverse g hg,?_⟩
  rw [realMobiusMatrix_inv,←hs,Mobius.fractionalLinear_inv_apply]

/-- Original P1 for every actual H ideal point and every actual horocycle at that point. -/
theorem existsUnique_hHorocycleAt_through (w : OnePoint ℂ) (hw : w∈halfPlaneIdealBoundary) (z : ℍ) :
    ∃!S : Set ℍ,IsHHorocycleAt w S ∧ z∈S := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  simpa only [isHHorocycleAt_chart_iff g hg] using existsUnique_chartHorocycle_through g z

/-- Original P2: there is no exceptional interior point for a genuine parabolic pencil. -/
theorem existsUnique_hParabolicPencil_through (w : OnePoint ℂ) (hw : w∈halfPlaneIdealBoundary) (z : ℍ) :
    ∃!L : HalfPlaneLine,L∈hParabolicPencil w ∧ z∈L.carrier := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  exact existsUnique_hParabolicPencil_chart_through g hg z

/-- Original P3 for actual complete generalized circles, for every actual ideal end. -/
theorem hHorocycleAt_orthogonal {w : OnePoint ℂ} (hw : w∈halfPlaneIdealBoundary)
    {L : HalfPlaneLine} (hL : L∈hParabolicPencil w) {S : Set ℍ} (hS : IsHHorocycleAt w S) :
    ∃C : Mobius.ComplexGeneralizedCircle, S=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  exact chartHorocycleFamily_orthogonal g hg L hL S ((isHHorocycleAt_chart_iff g hg S).mp hS)

/-- Original P4 for the actual native reflection in every pencil line. -/
theorem hHorocycleAt_reflection {w : OnePoint ℂ} (hw : w∈halfPlaneIdealBoundary)
    {L : HalfPlaneLine} (hL : L∈hParabolicPencil w) {S : Set ℍ} (hS : IsHHorocycleAt w S) :
    L.reflection '' S=S := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  exact chartHorocycleFamily_reflection g hg L hL S ((isHHorocycleAt_chart_iff g hg S).mp hS)

/-- Original P5, with the actual infimum over genuine curve-point pairs. -/
theorem hHorocycleAt_equidistance {w : OnePoint ℂ} (hw : w∈halfPlaneIdealBoundary)
    {S T : Set ℍ} (hS : IsHHorocycleAt w S) (hT : IsHHorocycleAt w T) (p : ℍ) (hp : p∈S) :
    ∃q : ℍ,q∈T ∧ dist p q=hCurveDistance S T ∧
      ∃L : HalfPlaneLine,L∈hParabolicPencil w ∧ p∈L.carrier ∧ q∈L.carrier := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  exact chartHorocycleFamily_equidistance g hg S T
    ((isHHorocycleAt_chart_iff g hg S).mp hS) ((isHHorocycleAt_chart_iff g hg T).mp hT) p hp

/-- Original P6 for actual distinct points, actual horocycles, and the genuine bisector. -/
theorem hParabolicPencil_perpendicularBisector_iff {w : OnePoint ℂ} (hw : w∈halfPlaneIdealBoundary)
    {a b : ℍ} (hab : a≠b) {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈hParabolicPencil w ↔ ∃S : Set ℍ,IsHHorocycleAt w S ∧ a∈S ∧ b∈S := by
  obtain ⟨g,hg,rfl⟩:=exists_hParabolicChart w hw
  simpa only [isHHorocycleAt_chart_iff g hg] using chartParabolicPencil_perpendicularBisector_iff g hg hab hN

end
end LowDimensionalTopology.Geometry.Hyperbolic
