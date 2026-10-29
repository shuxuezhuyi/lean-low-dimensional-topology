/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.ConcurrentHyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.DisjointHyperbolicDirections
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.EllipticFreeDiscreteness
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import Mathlib.Algebra.Order.Archimedean.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual hyperbolic translation length gives a pointwise lower bound for genuine half-sinh displacement. -/
theorem hHyperbolic_sinh_translation_le_displacement
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) (z : ℍ) :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)≤Real.sinh (dist z (A • z)/2) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement A hA ht z]
  have hs : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA ht])
  exact le_mul_of_one_le_left hs (Real.one_le_cosh _)

/-- The original sharp product bound when the two actual invariant axes cross. -/
theorem hEllipticFree_hyperbolic_crossing_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (p : ℍ) (hpA : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (hpB : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hneq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) (z : ℍ) :
    1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  let R:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).rayAt p hpA
  let S:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).rayAt p hpB
  have hR : R.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).rayAt_support p hpA
  have hS : S.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).rayAt_support p hpB
  have hRS : R.supportLine≠S.supportLine := by rwa [hR,hS]
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*A⁻¹*B⁻¹)∈G := by
    simpa only [map_mul,map_inv] using G.mul_mem
      (G.mul_mem (G.mul_mem hAm hBm) (G.inv_mem hAm)) (G.inv_mem hBm)
  have hb:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_commutator_intersection_bound A B hA hB htA htB R S hR hS
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos R S
      hRS) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_lt_pi R S hRS) (hG ⟨_,hm⟩)
  have hSA : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA])
  have hSB : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB])
  have hpair : 1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2) := by
    have hs:=Real.sin_le_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S)
    nlinarith [mul_nonneg hSA hSB]
  exact hpair.trans (mul_le_mul
    (hHyperbolic_sinh_translation_le_displacement A hA htA z)
    (hHyperbolic_sinh_translation_le_displacement B hB htB z) hSB
    (Real.sinh_nonneg_iff.mpr (by positivity)))

/-- Distinct crossing axes in an elliptic-free group give the sharp product
bound for the actual translation lengths. -/
theorem hEllipticFree_hyperbolic_crossing_translation_product
    (G : Subgroup complexMobiusGroup) (hG : IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : realSLMobius A ∈ G) (hBm : realSLMobius B ∈ G)
    (hA : realSLMobius A ≠ 1) (hB : realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val) ^ 2) (htB : 4 < (Matrix.trace B.val) ^ 2)
    (p : ℍ) (hpA : p ∈ (hHyperbolicAxis A hA htA).carrier)
    (hpB : p ∈ (hHyperbolicAxis B hB htB).carrier)
    (hneq : hHyperbolicAxis A hA htA ≠ hHyperbolicAxis B hB htB) :
    1 ≤ Real.sinh (hTranslationLength (hSLIsometry A) / 2) *
      Real.sinh (hTranslationLength (hSLIsometry B) / 2) := by
  have hb := hEllipticFree_hyperbolic_crossing_displacement_bound
    G hG A B hAm hBm hA hB htA htB p hpA hpB hneq p
  rw [(hHyperbolic_translation_minimum A hA htA p).mpr hpA,
    (hHyperbolic_translation_minimum B hB htB p).mpr hpB] at hb
  exact hb

/-- A pair of adjacent nonelliptic traces straddling zero imposes the exact multiplicative gap. -/
theorem ellipticFree_adjacent_exponential_gap (u x y : ℝ) (hu : 1<u)
    (hx : 0<x) (_hy : 0<y) (hyx : y≤x) (hxuy : x≤u^2*y)
    (hgap : 2≤|x-y|) (hgap' : 2≤|x/u-u*y|) :
    4*u≤x*y*(u-1)^2 := by
  rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hgap
  have hneg : x/u-u*y≤0 := by
    apply sub_nonpos.mpr
    apply (div_le_iff₀ (by linarith : 0<u)).mpr
    nlinarith
  rw [abs_of_nonpos hneg] at hgap'
  have hprev : 2*u≤u^2*y-x := by
    have he:=mul_le_mul_of_nonneg_right hgap' (by linarith : 0≤u)
    nlinarith [div_mul_cancel₀ x (by linarith : u≠0)]
  have hs : 0≤(u+1)*(y*(u-1)-2) := by nlinarith
  have hyl : 2≤y*(u-1) := by
    have hh:=nonneg_of_mul_nonneg_right hs (by linarith : 0<u+1)
    linarith
  have hxl : 2*u≤x*(u-1) := by nlinarith
  have hh:=mul_le_mul hxl hyl (by norm_num : (0:ℝ)≤2) (by positivity : 0≤x*(u-1))
  nlinarith

/-- Avoidance of the actual elliptic trace interval by every diagonal translate gives the sharp squared gap. -/
theorem ellipticFree_exponential_trace_gap (u a d : ℝ) (hu : 1<u) (ha : 0<a) (hd : d<0)
    (hgap : ∀n : ℤ,2≤|a*u^n+d*u^(-n)|) :
    4*u≤(-a*d)*(u-1)^2 := by
  have hu0 : 0<u:=by linarith
  let r:=Real.sqrt ((-d)/a)
  have hr : 0<r:=Real.sqrt_pos.mpr (div_pos (by linarith) ha)
  have hrsq : a*r^2= -d := by
    dsimp only [r]
    rw [Real.sq_sqrt (div_pos (neg_pos.mpr hd) ha).le]
    field_simp
  obtain ⟨n,hn0,hn1⟩:=exists_mem_Ico_zpow hr hu
  let v:=u^(n+1)
  have hv : 0<v:=zpow_pos hu0 _
  have hvn : v=u^n*u := by dsimp only [v];rw [zpow_add_one₀ hu0.ne']
  have hrv : r^2≤v^2 := by
    exact (sq_le_sq₀ hr.le hv.le).mpr hn1.le
  have hnr : (u^n)^2≤r^2 := by
    exact (sq_le_sq₀ (zpow_pos hu0 n).le hr.le).mpr hn0
  let x:=a*v
  let y:=(-d)/v
  have hx : 0<x:=mul_pos ha hv
  have hy : 0<y:=div_pos (by linarith) hv
  have hyx : y≤x := by
    apply (div_le_iff₀ hv).mpr
    have hh:=mul_le_mul_of_nonneg_left hrv ha.le
    dsimp only [x]
    nlinarith
  have hxuy : x≤u^2*y := by
    dsimp only [x,y]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hv).mpr
    have hh:=mul_le_mul_of_nonneg_left hnr ha.le
    have hhh:=mul_le_mul_of_nonneg_left hh (sq_nonneg u)
    rw [hvn]
    nlinarith
  have hcurrent : a*u^(n+1)+d*u^(-(n+1))=x-y := by
    rw [zpow_neg]
    change a*v+d*v⁻¹=a*v-(-d)/v
    ring
  have hprev : a*u^n+d*u^(-n)=x/u-u*y := by
    rw [zpow_neg]
    dsimp only [x,y]
    rw [hvn]
    field_simp
    ring
  have hg:=ellipticFree_adjacent_exponential_gap u x y hu hx hy hyx hxuy
    (by rw [←hcurrent];exact hgap (n+1)) (by rw [←hprev];exact hgap n)
  have hxy : x*y= -a*d := by
    dsimp only [x,y]
    field_simp
  rwa [hxy] at hg

/-- A crossing translate of the actual axis of a conjugate forces the sharp individual translation bound. -/
theorem hEllipticFree_intersecting_conjugate_translation_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hCm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hC :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htC : 4<(Matrix.trace C.val)^2)
    (hConj : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (p : ℍ) (hpA : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (hpC : p∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier)
    (hneq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) := by
  have hb:=hEllipticFree_hyperbolic_crossing_displacement_bound G hG A C hAm hCm hA hC htA htC
    p hpA hpC hneq p
  have hpdA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).pointDist p=0:=Metric.infDist_zero_of_mem hpA
  have hpdC : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC
    htC).pointDist p=0:=Metric.infDist_zero_of_mem hpC
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement A hA
    htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement C hC htC,
    hpdA,hpdC,Real.cosh_zero,one_mul,one_mul] at hb
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_eq_of_isConj A C hA hC htA htC
    hConj] at hb
  have hs : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA])
  nlinarith

/-- An actually nonsimple original hyperbolic element has the sharp individual translation bound. -/
theorem hEllipticFree_nonsimple_translation_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (hLift : ∀g∈G,∃A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA : 4<(Matrix.trace A.val)^2)
    (hns : ¬IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  have hex : ∃g∈G,
      (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace=>g • x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)≠_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
      ¬Disjoint ((fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace=>g • x)
        '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) := by
    by_contra hn
    apply hns
    refine ⟨hAm,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA,?_⟩
    intro g hg
    by_cases he : (fun x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace=>g • x) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
    · exact Or.inl he
    · exact Or.inr (by by_contra hd;exact hn ⟨g,hg,he,hd⟩)
  obtain ⟨g,hgm,hne,hnd⟩:=hex
  obtain ⟨q,rfl⟩:=hLift g hgm
  have hneq : (q • · : ℍ→ℍ) '' L.carrier≠L.carrier := by
    intro he
    apply hne
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,he]
  have hnotdisjoint : ¬Disjoint ((q • · : ℍ→ℍ) '' L.carrier) L.carrier := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,
      Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective] using hnd
  obtain ⟨p,hpq,hp⟩:=Set.not_disjoint_iff.mp hnotdisjoint
  let C:=q*A*q⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A q hA
  have htC : 4<(Matrix.trace C.val)^2 := by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈G := by
    simpa only [C,map_mul,map_inv] using G.mul_mem (G.mul_mem hgm hAm) (G.inv_mem hgm)
  have hConj : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by
    apply isConj_iff.mpr
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q,by simp only [C,map_mul,map_inv]⟩
  have hCaxis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier=(q • · : ℍ→ℍ) '' L.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  apply hEllipticFree_intersecting_conjugate_translation_bound G hG A C hAm hCm hA hC htA htC hConj p hp
  · rwa [hCaxis]
  · intro he
    apply hneq
    rw [←hCaxis,←he]

/-- The original sharp product bound when both original elements are nonsimple. -/
theorem hEllipticFree_both_nonsimple_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (hLift : ∀g∈G,∃A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hnsA : ¬IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hnsB : ¬IsSimple G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) (z : ℍ) :
    1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  have ha:=(hEllipticFree_nonsimple_translation_bound G hG hLift A hAm hA htA hnsA).trans
    (hHyperbolic_sinh_translation_le_displacement A hA htA z)
  have hb:=(hEllipticFree_nonsimple_translation_bound G hG hLift B hBm hB htB hnsB).trans
    (hHyperbolic_sinh_translation_le_displacement B hB htB z)
  nlinarith

end LowDimensionalTopology.Geometry.Fuchsian
