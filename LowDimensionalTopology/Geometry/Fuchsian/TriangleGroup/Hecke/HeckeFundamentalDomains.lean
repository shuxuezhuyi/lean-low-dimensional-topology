/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleConformalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeUnitNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The symmetric vertical strip outside the unit semicircle in the upper half-plane. -/
def standardHeckeDomain (q : ℕ∞) (_hq : 3≤q) : Set ℍ:=
  {z | |z.re|<Real.cos (triangleOrderAngle q) ∧ 1<‖(z:ℂ)‖}

theorem native_realAxis_interior_empty : interior {z:ℍ | z.re=0}=∅ := by
  have h:=UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage
    UpperHalfPlane.continuous_re ({0}:Set ℝ)
  have he : UpperHalfPlane.re ⁻¹' ({0}:Set ℝ)={z:ℍ|z.re=0}:=by ext z;simp
  rw [he,interior_singleton,preimage_empty] at h
  exact h.symm

theorem standardHeckeDomain_isOpen (q : ℕ∞) (hq : 3≤q) : IsOpen (standardHeckeDomain q hq) :=
  (isOpen_lt UpperHalfPlane.continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_const UpperHalfPlane.continuous_coe.norm)

theorem standardHeckeDomain_axis_invariant (q : ℕ∞) (hq : 3≤q) (z : ℍ) :
    idealTriangleAxisMirror z∈standardHeckeDomain q hq ↔ z∈standardHeckeDomain q hq := by
  change (|(idealTriangleAxisMirror z).re|<_ ∧ 1<‖(idealTriangleAxisMirror z:ℂ)‖) ↔
    (|z.re|<_ ∧ 1<‖(z:ℂ)‖)
  rw [idealTriangleAxisMirror_re,idealTriangleAxisMirror_coe]
  simp only [abs_neg,norm_neg,Complex.norm_conj]

theorem standardHeckeTriangle_subset_domain (q : ℕ∞) (hq : 3≤q) :
    (standardHeckeTriangle q hq).interior⊆standardHeckeDomain q hq := by
  intro z hz
  have h:= (prescribedIdealHTriangle_mem_interior_iff _ _ _ _ _ z).mp hz
  rw [Real.cos_pi_div_two,neg_zero] at h
  change |z.re|<_ ∧ 1<‖(z:ℂ)‖
  exact ⟨by rw [abs_of_pos h.1.1];exact h.1.2,by nlinarith [norm_nonneg (z:ℂ)]⟩

theorem standardHeckeDomain_fold (q : ℕ∞) (hq : 3≤q) (z : ℍ)
    (hz : z∈standardHeckeDomain q hq) (hne : z.re≠0) :
    z∈(standardHeckeTriangle q hq).interior ∨
      idealTriangleAxisMirror z∈(standardHeckeTriangle q hq).interior := by
  have hpos (w : ℍ) (hw:w∈standardHeckeDomain q hq) (hw0:0<w.re) :
      w∈(standardHeckeTriangle q hq).interior:=by
    apply (prescribedIdealHTriangle_mem_interior_iff _ _ _ _ _ w).mpr
    rw [Real.cos_pi_div_two,neg_zero]
    exact ⟨⟨hw0,(le_abs_self _).trans_lt hw.1⟩,by nlinarith [hw.2]⟩
  rcases lt_or_gt_of_ne hne with hneg|hpos0
  · right
    apply hpos _ ((standardHeckeDomain_axis_invariant q hq z).mpr hz)
    rw [idealTriangleAxisMirror_re]
    linarith
  · exact Or.inl (hpos z hz hpos0)

theorem standardHecke_axis_mem_reflectionGroup (q : ℕ∞) (hq : 3≤q) :
    idealTriangleAxisMirror∈triangleReflectionGroup (standardHeckeTriangle q hq) := by
  apply Subgroup.subset_closure
  refine ⟨(standardHeckeTriangle q hq).sideLineB,?_,?_⟩
  · simp [triangleReflectionSides]
  · rw [standardHeckeTriangle,prescribedIdealHTriangle_sideB,Real.cos_pi_div_two,neg_zero]
    rfl

/-- Every nonidentity original Hecke element separates the literal figure domain from itself. -/
theorem standardHeckeDomain_packing (q : ℕ∞) (hq : 3≤q) (g : ℍ≃ᵢℍ)
    (hg : g∈standardHeckeGroup q hq) (hne : g≠1) :
    Disjoint (g • standardHeckeDomain q hq) (standardHeckeDomain q hq) := by
  let T:=standardHeckeTriangle q hq
  let B:=idealTriangleAxisMirror
  have hB : B∈triangleReflectionGroup T:=standardHecke_axis_mem_reflectionGroup q hq
  have hBi : B⁻¹=B:=halfPlaneLineReflectionIsometry_inv _
  have hBB : B*B=1:=by
    apply IsometryEquiv.ext
    intro z
    exact idealTriangleAxisMirror_involutive z
  have hBnot : B∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=halfPlaneLineReflectionIsometry_not_conformal _
  have hOne (k : ℍ≃ᵢℍ) (hk : k∈triangleReflectionGroup T) (z : ℍ)
      (hz:z∈T.interior) (hkz:k z∈T.interior) : k=1:=by
    by_contra hn
    have hp:=prescribedIdealHTriangle_reflection_packing (Real.pi/2) (triangleOrderAngle q)
      (Or.inr ⟨2,by norm_num,by norm_num⟩) (triangleOrderAngle_isIntegral q (le_trans (by norm_num) hq))
      (by have h:=(hecke_order_angle_bounds q hq).2;linarith only [h,Real.pi_pos]) k hk hn
    exact disjoint_left.mp hp ⟨z,hz,rfl⟩ hkz
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hgx
  let U:=standardHeckeDomain q hq∩g ⁻¹' standardHeckeDomain q hq
  have hU : IsOpen U:=(standardHeckeDomain_isOpen q hq).inter
    ((standardHeckeDomain_isOpen q hq).preimage g.continuous)
  have hxU : x∈U:=⟨hx,hgx⟩
  let Z:Set ℍ:={z|z.re=0}∪g ⁻¹' {z|z.re=0}
  have hZ : interior Z=∅:=by
    have hp : interior (g ⁻¹' {z:ℍ|z.re=0})=∅:=by
      change interior (g.toHomeomorph ⁻¹' {z:ℍ|z.re=0})=∅
      rw [←g.toHomeomorph.preimage_interior,native_realAxis_interior_empty,preimage_empty]
    rw [interior_union_isClosed_of_interior_empty
      (isClosed_eq UpperHalfPlane.continuous_re continuous_const) hp,native_realAxis_interior_empty]
  have hy : ∃y∈U,y∉Z:=by
    by_contra! hh
    have hs : U⊆interior Z:=hU.subset_interior_iff.mpr hh
    simpa only [hZ,mem_empty_iff_false] using hs hxU
  obtain ⟨y,hy,hyn⟩:=hy
  have hy0 : y.re≠0:=fun hh=>hyn (Or.inl hh)
  have hgy0 : (g y).re≠0:=fun hh=>hyn (Or.inr hh)
  have hgFull : g∈triangleReflectionGroup T:=hg.1
  rcases standardHeckeDomain_fold q hq y hy.1 hy0 with hyA|hyB <;>
    rcases standardHeckeDomain_fold q hq (g y) hy.2 hgy0 with hgyA|hgyB
  · exact hne (hOne g hgFull y hyA hgyA)
  · have he : B*g=1:=hOne (B*g) ((triangleReflectionGroup T).mul_mem hB hgFull) y hyA hgyB
    have heq : g=B:=by calc
      g=B⁻¹*(B*g):=by group
      _=B:=by rw [he,mul_one,hBi]
    exact hBnot (heq ▸ hg.2)
  · have he : g*B=1:=hOne (g*B) ((triangleReflectionGroup T).mul_mem hgFull hB) (B y) hyB
      (by simpa only [IsometryEquiv.mul_apply,show ∀z,B (B z)=z from idealTriangleAxisMirror_involutive] using hgyA)
    have heq : g=B:=by calc
      g=(g*B)*B⁻¹:=by group
      _=B:=by rw [he,one_mul,hBi]
    exact hBnot (heq ▸ hg.2)
  · have he : B*g*B=1:=hOne (B*g*B)
      ((triangleReflectionGroup T).mul_mem ((triangleReflectionGroup T).mul_mem hB hgFull) hB)
      (B y) hyB (by simpa only [IsometryEquiv.mul_apply,show ∀z,B (B z)=z from idealTriangleAxisMirror_involutive] using hgyB)
    apply hne
    calc
      g=B⁻¹*(B*g*B)*B⁻¹:=by group
      _=1:=by rw [he,mul_one,hBi,hBB]


/-- The figure region is hyperbolically convex in the original native metric. -/
theorem standardHeckeDomain_hConvex
    (q : ℕ∞)
    (hq : 3≤q) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (standardHeckeDomain q hq) := by
  intro z hz w hw u hu
  have hpos : u.re<Real.cos (triangleOrderAngle q):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex _ z (abs_lt.mp hz.1).2 w (abs_lt.mp hw.1).2 hu
  have hneg : (idealTriangleAxisMirror u).re<Real.cos (triangleOrderAngle q):=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex _) idealTriangleAxisMirror.isometry z ?_ w ?_ hu
    · change (idealTriangleAxisMirror z).re<_
      rw [idealTriangleAxisMirror_re]
      linarith [(abs_lt.mp hz.1).1]
    · change (idealTriangleAxisMirror w).re<_
      rw [idealTriangleAxisMirror_re]
      linarith [(abs_lt.mp hw.1).1]
  rw [idealTriangleAxisMirror_re] at hneg
  have hnorm : 1<‖(u:ℂ)‖:=by
    have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_outside_circle 0 1 zero_lt_one z
      (by simpa using hz.2) w (by simpa using hw.2) hu
    simpa using he
  exact ⟨abs_lt.mpr ⟨by linarith,hpos⟩,hnorm⟩

/-- Every original Hecke orbit meets the closure of the literal centered-strip domain. -/
theorem standardHeckeDomain_closure_meetsEveryOrbit (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (standardHeckeGroup q hq) ℍ (closure (standardHeckeDomain q hq)) := by
  let T:=standardHeckeTriangle q hq
  let B:=idealTriangleAxisMirror
  have hT:=standardHeckeTriangle_subset_domain q hq
  have hB : B∈triangleReflectionGroup T:=standardHecke_axis_mem_reflectionGroup q hq
  have hM : MapsTo B T.interior (standardHeckeDomain q hq):=by
    intro z hz
    exact (standardHeckeDomain_axis_invariant q hq z).mpr (hT hz)
  have hCover : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (triangleReflectionGroup T) ℍ (closure T.interior):=
    prescribedIdealHTriangle_closure_meetsEveryOrbit (Real.pi/2) (triangleOrderAngle q)
      (Or.inr ⟨2,by norm_num,by norm_num⟩)
      (triangleOrderAngle_isIntegral q (le_trans (by norm_num) hq))
      (by have h:=(hecke_order_angle_bounds q hq).2;linarith only [h,Real.pi_pos])
  intro x
  obtain ⟨g,hg⟩:=hCover x
  rcases native_conformal_or_axis_mul_conformal g.val with hconf|hconf
  · refine ⟨⟨g.val,⟨g.property,hconf⟩⟩,?_⟩
    exact closure_mono hT hg
  · refine ⟨⟨B*g.val,⟨(triangleReflectionGroup T).mul_mem hB g.property,hconf⟩⟩,?_⟩
    change B (g.val x)∈closure (standardHeckeDomain q hq)
    exact map_mem_closure B.continuous hg hM

/-- The boundary of the standard Hecke domain lies on three hyperbolic geodesics. -/
theorem standardHeckeDomain_frontier_volume_zero (q : ℕ∞) (hq : 3≤q) :
    volume (frontier (standardHeckeDomain q hq))=0 := by
  let c:=Real.cos (triangleOrderAngle q)
  let L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.vertical (-c)
  let R:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.vertical c
  let C:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.circle 0 1 zero_lt_one
  have hsub : frontier (standardHeckeDomain q hq)⊆L.carrier∪R.carrier∪C.carrier:=by
    intro z hz
    have hf : z∈frontier {z : ℍ | |z.re| < c} ∪ frontier {z:ℍ|1<‖(z:ℂ)‖}:=
      (frontier_inter_subset _ _ hz).elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.2)
    rcases hf with hl|hc
    · have he : |z.re|=c:=frontier_lt_subset_eq UpperHalfPlane.continuous_re.abs continuous_const hl
      rcases le_total 0 z.re with hp|hn
      · exact Or.inl (Or.inr (by change z.re=c;simpa only [abs_of_nonneg hp] using he))
      · exact Or.inl (Or.inl (by change z.re= -c;rw [abs_of_nonpos hn] at he;linarith))
    · right
      have he : (1:ℝ)=‖(z:ℂ)‖:=frontier_lt_subset_eq continuous_const UpperHalfPlane.continuous_coe.norm hc
      change ‖(z:ℂ)-(0:ℂ)‖=1
      simpa using he.symm
  exact measure_mono_null hsub (measure_union_null (measure_union_null L.volume_zero R.volume_zero) C.volume_zero)

/-- The standard Hecke domain is a fundamental domain for the standard Hecke group,
including the infinite-order parameter. -/
theorem standardHeckeDomain_fundamentalDomain (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (standardHeckeGroup q hq) ℍ volume (standardHeckeDomain q hq) := by
  have hn : (standardHeckeDomain q hq).Nonempty:=
    (standardHeckeTriangle q hq).interior_nonempty.mono (standardHeckeTriangle_subset_domain q hq)
  refine ⟨standardHeckeDomain_isOpen q hq,⟨hn,(standardHeckeDomain_hConvex q hq).isPreconnected⟩,?_,
    standardHeckeDomain_frontier_volume_zero q hq⟩
  apply exists_fundamentalSet_between _ _ subset_closure (standardHeckeDomain_closure_meetsEveryOrbit q hq)
  intro x hx y hy he
  obtain ⟨g,hg⟩:=(Quotient.exact he : MulAction.orbitRel (standardHeckeGroup q hq) ℍ x y)
  by_cases h1 : g.val=1
  · simpa only [show g=1 from Subtype.ext h1,one_smul] using hg.symm
  · exact False.elim (disjoint_left.mp (standardHeckeDomain_packing q hq g.val g.property h1)
      ⟨y,hy,hg⟩ hx)


/-- The same actual figure domain after the original parabolic generator is rescaled to unit translation. -/
def unitHeckeDomain (q : ℕ∞) (_hq : 3≤q) : Set ℍ:=
  {z | |z.re|<(1:ℝ)/2 ∧ 1/(2*Real.cos (triangleOrderAngle q))<‖(z:ℂ)‖}

/-- The true positive native dilation carries the literal standard domain exactly onto the literal unit domain. -/
theorem unitHeckeDomain_image (q : ℕ∞) (hq : 3≤q) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)) '' standardHeckeDomain q hq=unitHeckeDomain q hq := by
  let c:=Real.cos (triangleOrderAngle q)
  have hc : 0<c:=by have h:=hecke_width_pos q hq;change 0<2*c at h;linarith
  let s:=1/(2*c)
  have hs : 0<s:=one_div_pos.mpr (mul_pos (by norm_num) hc)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)
  have he (z : ℍ) : (D z:ℂ)=(s:ℂ)*(z:ℂ):=by
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe _ _ z
  have hre (z : ℍ) : (D z).re=s*z.re:=by
    have hh:=congrArg Complex.re (he z)
    simpa using hh
  have hnorm (z : ℍ) : ‖(D z:ℂ)‖=s*‖(z:ℂ)‖:=by
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  have hsc : s*c=(1:ℝ)/2:=by dsimp [s];field_simp
  have hp : D ⁻¹' unitHeckeDomain q hq=standardHeckeDomain q hq:=by
    ext z
    change (|(D z).re|<(1:ℝ)/2 ∧ s<‖(D z:ℂ)‖) ↔ (|z.re|<c ∧ 1<‖(z:ℂ)‖)
    rw [hre,hnorm,abs_mul,abs_of_pos hs,←hsc]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hs).mp h1,(mul_lt_mul_iff_right₀ hs).mp (by simpa using h2)⟩
    · rintro ⟨h1,h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hs).mpr h1,by simpa using (mul_lt_mul_iff_right₀ hs).mpr h2⟩
  calc
    _ = D '' (D ⁻¹' unitHeckeDomain q hq) := by rw [hp]
    _ = _ := D.toEquiv.image_preimage _

/-- The literal unit-normalized Hecke domain is a genuine fundamental domain for every parameter. -/
theorem unitHeckeDomain_fundamentalDomain (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (unitHeckeGroup q hq) ℍ volume (unitHeckeDomain q hq) := by
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL q hq)
  have hConj : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D⁻¹ (unitHeckeGroup q hq)=standardHeckeGroup q hq:=by
    rw [unitHeckeGroup,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one]
  have hFD:=standardHeckeDomain_fundamentalDomain q hq
  rw [←hConj] at hFD
  have h:=native_fundamentalDomain_conjugate_preimage _ D⁻¹ hFD
  have he : ((D⁻¹ : ℍ≃ᵢℍ) ⁻¹' standardHeckeDomain q hq)=unitHeckeDomain q hq:=by
    rw [←unitHeckeDomain_image]
    exact (D.toEquiv.image_eq_preimage_symm _).symm
  rwa [he] at h

end LowDimensionalTopology.Geometry.Fuchsian
