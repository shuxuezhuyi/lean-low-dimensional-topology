/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleCornerSectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ComplexConjugate
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

/-- Conjugating the original right corner by the actual axis mirror gives the original left corner. -/
theorem idealTriangleLeftConjugation_corner_general (θ : ℝ) :
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL θ))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos θ)*modularInversionSL) := by
  have hT : idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos θ)))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos θ)):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos θ))*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹=_
    simpa only [neg_mul] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_axis_reflection_conjugation (2*Real.cos θ)
  change idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_)
  rw [map_mul,map_mul,map_mul]
  change idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos θ)))*
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos θ))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL
  rw [hT,idealTriangleLeftConjugation_inversion]

theorem prescribedIdealHTriangle_right_product (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (prescribedIdealHTriangle α β hα hβ hs).sideLineA
      (prescribedIdealHTriangle α β hα hβ hs).sideLineC=idealCornerSL β := by
  rw [prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,idealCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem prescribedIdealHTriangle_left_product (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (prescribedIdealHTriangle α β hα hβ hs).sideLineB
      (prescribedIdealHTriangle α β hα hβ hs).sideLineC=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos α)*modularInversionSL := by
  rw [prescribedIdealHTriangle_sideB,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- The actual conformal group is the group generated by its two physical corners. -/
theorem prescribedIdealHTriangle_conformal_eq_twoCornerGroup (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    triangleConformalGroup (prescribedIdealHTriangle α β hα hβ hs)=idealTwoCornerGroup α β := by
  rw [triangleConformalGroup_eq_crossPairProducts,reflectionProductSL_native,
    reflectionProductSL_native,prescribedIdealHTriangle_left_product,
    prescribedIdealHTriangle_right_product,←idealTriangleLeftConjugation_corner_general]
  change Subgroup.closure _=(Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL α))).map
    idealTriangleLeftConjugation⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL β))
  rw [MonoidHom.map_zpowers]
  rw [←Set.singleton_union,Subgroup.closure_union,←Subgroup.zpowers_eq_closure,←Subgroup.zpowers_eq_closure]

/-- The two-sector middle gap is invariant under the original third mirror. -/
theorem idealTwoCornerGap_circleReflection_iff (α β : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z∈idealTwoCornerGap α β ↔ z∈idealTwoCornerGap α β := by
  change (idealTriangleAxisMirror (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z)∈idealCornerSector α ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z∈idealCornerSector β) ↔
    (idealTriangleAxisMirror z∈idealCornerSector α ∧ z∈idealCornerSector β)
  rw [idealTriangleAxisMirror_circleReflection,idealCornerSector_circleReflection_iff,
    idealCornerSector_circleReflection_iff]

/-- The literal original triangle lies inside its genuine two-corner gap. -/
theorem prescribedIdealHTriangle_interior_subset_gap (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior⊆idealTwoCornerGap α β := by
  intro z hz
  have hi:=(prescribedIdealHTriangle_mem_interior_iff α β hα.nonneg hβ.nonneg hs z).mp hz
  have ha:=hα.cos_nonneg
  have hb:=hβ.cos_nonneg
  have he : Complex.normSq (idealTriangleAxisMirror z:ℂ)=Complex.normSq (z:ℂ):=by
    rw [idealTriangleAxisMirror_coe]
    simp
  constructor
  · change (idealTriangleAxisMirror z).re<Real.cos α ∧
      (idealTriangleAxisMirror z).re<Real.cos α*Complex.normSq (idealTriangleAxisMirror z:ℂ)
    rw [idealTriangleAxisMirror_re,he,Complex.normSq_eq_norm_sq]
    have hmul:=mul_nonneg ha (sub_nonneg.mpr hi.2.le)
    exact ⟨by linarith [hi.1.1],by nlinarith [hi.1.1]⟩
  · change z.re<Real.cos β ∧ z.re<Real.cos β*Complex.normSq (z:ℂ)
    rw [Complex.normSq_eq_norm_sq]
    have hmul:=mul_nonneg hb (sub_nonneg.mpr hi.2.le)
    exact ⟨hi.1.2,by nlinarith [hi.1.2]⟩

/-- Every nontrivial original conformal group element separates the literal triangle interior. -/
theorem prescribedIdealHTriangle_conformal_packing (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi)
    (g : ℍ≃ᵢℍ)
    (hg : g∈triangleConformalGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs))
    (hne : g≠1) :
    Disjoint (g • (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior)
      (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  rw [prescribedIdealHTriangle_conformal_eq_twoCornerGroup] at hg
  exact (idealTwoCornerGap_wandering α β hα hβ hs g hg hne).mono
    (smul_set_subset_smul_set_iff.mpr (prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs))
    (prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs)


/-- The actual full reflection group is the conformal group together with its original third-mirror coset. -/
theorem triangleReflectionGroup_conformal_or_thirdMirror
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (g : ℍ≃ᵢℍ)
    (hg : g∈triangleReflectionGroup T) :
    g∈triangleConformalGroup T ∨
      g*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC∈triangleConformalGroup T := by
  obtain ⟨l,_hl,he⟩:=(triangleReflectionGroup_mem_iff_word T g).mp hg
  have hword : ((l++[T.sideLineC]).map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod=
      g*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC:=by simp [he]
  have hpar : g*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ↔
      ¬g∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=by
    rw [←hword,←he,halfPlane_reflectionWord_conformal_iff_even,
      halfPlane_reflectionWord_conformal_iff_even]
    simp only [List.length_append,List.length_singleton,Nat.even_add_one]
  by_cases hconf : g∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  · exact Or.inl ⟨hg,hconf⟩
  · right
    refine ⟨(triangleReflectionGroup T).mul_mem hg ?_,hpar.mpr hconf⟩
    exact Subgroup.subset_closure ⟨T.sideLineC,by simp [triangleReflectionSides],rfl⟩

/-- Genuine full-group packing of the original open triangle, including all ideal vertex cases. -/
theorem prescribedIdealHTriangle_reflection_packing (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi)
    (g : ℍ≃ᵢℍ)
    (hg : g∈triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs))
    (hne : g≠1) :
    Disjoint (g • (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior)
      (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  rcases triangleReflectionGroup_conformal_or_thirdMirror T g hg with hconf|hconf
  · exact prescribedIdealHTriangle_conformal_packing α β hα hβ hs g hconf hne
  · apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ hgcx
    have hxGap:=prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs hx
    have hgGap:=prescribedIdealHTriangle_interior_subset_gap α β hα hβ hs hgcx
    have hc : ∀z,c z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z:=by
      intro z
      dsimp only [c]
      rw [prescribedIdealHTriangle_circle]
      rfl
    by_cases h1 : g*c=1
    · have he : g=c:=by
        have hcInv : c⁻¹=c:=halfPlaneLineReflectionIsometry_inv _
        exact (mul_eq_one_iff_eq_inv.mp h1).trans hcInv
      have hi:=(prescribedIdealHTriangle_mem_interior_iff α β hα.nonneg hβ.nonneg hs x).mp hx
      have hj:=(prescribedIdealHTriangle_mem_interior_iff α β hα.nonneg hβ.nonneg hs (g x)).mp hgcx
      rw [he,hc,unitCircleReflection_norm_sq] at hj
      have hn : 0<‖(x:ℂ)‖^2:=lt_trans zero_lt_one hi.2
      have hh := (inv_lt_one₀ hn).mpr hi.2
      exact (not_lt_of_ge hh.le) hj.2
    · rw [prescribedIdealHTriangle_conformal_eq_twoCornerGroup] at hconf
      have hd:=idealTwoCornerGap_wandering α β hα hβ hs (g*c) hconf h1
      have hxC : c x∈idealTwoCornerGap α β:=by
        rw [hc]
        exact (idealTwoCornerGap_circleReflection_iff α β x).mpr hxGap
      apply disjoint_left.mp hd ?_ hgGap
      refine ⟨c x,hxC,?_⟩
      change g (c (c x))=g x
      have hcc : c (c x)=x:=by
        change T.sideLineC.reflection (T.sideLineC.reflection x)=x
        exact T.sideLineC.reflection_involutive x
      rw [hcc]

/-- Literal original open-triangle points cannot represent the same orbit twice. -/
theorem prescribedIdealHTriangle_orbit_unique (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi)
    (x y : ℍ)
    (hx : x∈(prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior)
    (hy : y∈(prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ x=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ y) : x=y := by
  obtain ⟨g,hg⟩:=(Quotient.exact he : MulAction.orbitRel
    (triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ x y)
  by_cases h1 : g.val=1
  · simpa only [show g=1 from Subtype.ext h1,one_smul] using hg.symm
  · exact False.elim (disjoint_left.mp (prescribedIdealHTriangle_reflection_packing α β hα hβ hs
      g.val g.property h1) ⟨y,hy,hg⟩ hx)

/-- Every original full-group orbit meets the actual closure of the ideal triangle. -/
theorem prescribedIdealHTriangle_closure_meetsEveryOrbit (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ
      (closure (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior) := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  have hangle:=prescribedIdealHTriangle_angles α β hα.nonneg hβ.nonneg hs
  let : DiscreteTopology (triangleReflectionGroup T):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_integral_angles T
      (hangle.1.symm ▸ hα) (hangle.2.1.symm ▸ hβ) (hangle.2.2.symm ▸ (Or.inl rfl))
  have hd:=triangleReflectionGroup_discontinuous T
  obtain ⟨w,hw⟩:=T.interior_nonempty
  intro x
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit (triangleReflectionGroup T) hd w x
  exact ⟨g,prescribedIdealHTriangle_closedDirichlet_subset α β hα.nonneg hβ.nonneg hs w hw hg⟩

/-- The actual native hyperbolic-area frontier is null, even at cusps. -/
theorem prescribedIdealHTriangle_frontier_volume_zero (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    MeasureTheory.volume (frontier (prescribedIdealHTriangle α β hα hβ hs).interior)=0 := by
  let T:=prescribedIdealHTriangle α β hα hβ hs
  let L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.vertical (-Real.cos α)
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.vertical (Real.cos β)
  let C : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.circle 0 1 zero_lt_one
  have hsub : frontier T.interior⊆L.carrier∪R.carrier∪C.carrier:=by
    rw [frontier,T.interior_isOpen.interior_eq]
    rintro z ⟨hz,hnot⟩
    have hc:=hz
    rw [prescribedIdealHTriangle_interior_closure] at hc
    by_cases hL : z.re= -Real.cos α
    · exact Or.inl (Or.inl hL)
    by_cases hR : z.re=Real.cos β
    · exact Or.inl (Or.inr hR)
    by_cases hC : ‖(z:ℂ)‖^2=1
    · right
      change ‖(z:ℂ)-(0:ℂ)‖=1
      simp only [sub_zero]
      nlinarith [norm_nonneg (z:ℂ)]
    exact False.elim (hnot ((prescribedIdealHTriangle_mem_interior_iff α β hα hβ hs z).mpr
      ⟨⟨lt_of_le_of_ne hc.1.1 (Ne.symm hL),lt_of_le_of_ne hc.1.2 hR⟩,
        lt_of_le_of_ne hc.2 (Ne.symm hC)⟩))
  exact measure_mono_null hsub (measure_union_null (measure_union_null L.volume_zero R.volume_zero) C.volume_zero)

/-- The genuine original ideal triangle is a fundamental domain for its entire reflection group,
including one, two, and three ideal vertices. -/
theorem prescribedIdealHTriangle_fundamentalDomain (α β : ℝ)
    (hα : IsIntegralTriangleAngle α) (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (triangleReflectionGroup (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs)) ℍ
      MeasureTheory.volume (prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs).interior := by
  let T:=prescribedIdealHTriangle α β hα.nonneg hβ.nonneg hs
  refine ⟨T.interior_isOpen,⟨T.interior_nonempty,T.interior_isPreconnected⟩,?_,
    prescribedIdealHTriangle_frontier_volume_zero α β hα.nonneg hβ.nonneg hs⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (prescribedIdealHTriangle_closure_meetsEveryOrbit α β hα hβ hs)
    (fun x hx y hy he=>prescribedIdealHTriangle_orbit_unique α β hα hβ hs x y hx hy he)

end LowDimensionalTopology.Geometry.Fuchsian
