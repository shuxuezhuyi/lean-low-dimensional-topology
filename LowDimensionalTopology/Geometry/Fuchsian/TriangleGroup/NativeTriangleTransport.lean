/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleFundamentalDomains
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

/-- Every genuine native isometry preserves the original density-defined hyperbolic area. -/
theorem native_isometry_volume_image (f : ℍ≃ᵢℍ) (S : Set ℍ) :
    volume (f '' S)=volume S := by
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL f.isometry
  rw [hg]
  exact measure_smul (volume:Measure ℍ) g S

theorem native_isometry_volume_map (f : ℍ≃ᵢℍ) :
    Measure.map f (volume:Measure ℍ)=volume := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply f.continuous.measurable hS]
  have he : f ⁻¹' S=f.symm '' S:=(f.toEquiv.symm.image_eq_preimage_symm S).symm
  rw [he]
  exact native_isometry_volume_image f.symm S

/-- Fundamental domains transport with the actual conjugate group and the same original density measure. -/
theorem native_fundamentalDomain_conjugate_preimage (H : Subgroup (ℍ≃ᵢℍ)) (f : ℍ≃ᵢℍ)
    {S : Set ℍ} (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate f H) ℍ volume S) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (f ⁻¹' S) := by
  let E:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence f H
  have he (g : H) (z : ℍ) : f.toHomeomorph (g • z)=E g • f.toHomeomorph z:=by
    change f (g.val z)=f (g.val (f⁻¹ (f z)))
    rw [IsometryEquiv.inv_apply_self]
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage E f.toHomeomorph he hS
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ (Measure.map f.symm volume) (f ⁻¹' S) at h
  rwa [native_isometry_volume_map f.symm] at h


theorem idealTriangleAxisMirror_im (z : ℍ) : (idealTriangleAxisMirror z).im=z.im := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z).im=z.im
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_im 0 z

/-- The physical axis mirror reverses exactly the original real graph-strip endpoints. -/
theorem idealTriangleAxisMirror_graph_image (a b : ℝ) :
    idealTriangleAxisMirror '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo a b)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo (-b) (-a)) := by
  have hf (a b : ℝ) (z : ℍ) (hz:z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo a b)) :
      idealTriangleAxisMirror z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2)) (Ioo (-b) (-a)):=by
    change ((idealTriangleAxisMirror z).re∈Ioo (-b) (-a) ∧
      Real.sqrt (1-(idealTriangleAxisMirror z).re^2)<(idealTriangleAxisMirror z).im)
    rw [idealTriangleAxisMirror_re,idealTriangleAxisMirror_im,neg_sq]
    exact ⟨⟨neg_lt_neg hz.1.2,neg_lt_neg hz.1.1⟩,hz.2⟩
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hf a b x hx
  · intro hz
    refine ⟨idealTriangleAxisMirror z,?_,idealTriangleAxisMirror_involutive z⟩
    simpa only [neg_neg] using hf (-b) (-a) z hz

/-- The actual prescribed three-reflection group is the canonical normalized side group. -/
theorem prescribedIdealHTriangle_reflection_eq_normalized (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (hs : α+β<Real.pi) :
    triangleReflectionGroup (prescribedIdealHTriangle α β hα hβ hs)=
      normalizedIdealTriangleGroup (-Real.cos α) (Real.cos β) := by
  unfold triangleReflectionGroup triangleReflectionSides
  rw [prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_sideB,prescribedIdealHTriangle_circle]
  simp only [image_insert_eq,image_singleton]
  change normalizedIdealTriangleGroup (Real.cos β) (-Real.cos α)=_
  exact normalizedIdealTriangleGroup_swap _ _

/-- A genuine ideal triangle has one actual native normalization carrying both the entire group
and the literal original open triangle to their canonical physical counterparts. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.ideal_group_and_interior_canonical
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hγ : T.gamma=0) :
    ∃e:ℍ≃ᵢℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T)=
        normalizedIdealTriangleGroup (-Real.cos T.alpha) (Real.cos T.beta) ∧
      e '' T.interior=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2))
        (Ioo (-Real.cos T.alpha) (Real.cos T.beta)) := by
  have hci : ‖(T.toDiscTriangle.c:ℂ)‖=1:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr (closed_triangle_gamma_zero_ideal T hγ)
  obtain ⟨g,hg,hpEnd,hline⟩:=T.toDiscTriangle.exists_ideal_vertex_area_normalizer hci
  obtain ⟨a,b,hna,hnb,_hia,_hib,hne,ha,hb,hA,hB⟩:=
    T.toDiscTriangle.normalized_sides_and_vertices hci g hg hpEnd hline
  have heA : T.sideLineA.realGLMap g=.vertical b.re:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hA
  have heB : T.sideLineB.realGLMap g=.vertical a.re:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hB
  have heC : T.sideLineC.realGLMap g=.circle 0 1 zero_lt_one:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hline
  have hG:= (triangle_reflectionGroup_conjugate_of_side_images T g _ _ _ heA heB heC).trans
    (normalizedIdealTriangleGroup_swap b.re a.re)
  have hα:=T.toDiscTriangle.alpha_cos_normalized hci g hg hline hpEnd a b hna hnb hne ha hb
  have hβ:=T.toDiscTriangle.beta_cos_normalized hci g hg hline hpEnd a b hna hnb hne ha hb
  have hI:=T.toDiscTriangle.normalized_interior_eq_graph hci g hg hpEnd hline a b hna hnb hne ha hb hA hB
  change Real.cos T.alpha=(if a.re<b.re then -a.re else a.re) at hα
  change Real.cos T.beta=(if b.re<a.re then -b.re else b.re) at hβ
  change (fun z:ℍ=>g • z) '' T.interior=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x=>Real.sqrt (1-x^2))
    (Ioo (min a.re b.re) (max a.re b.re)) at hI
  by_cases hab : a.re<b.re
  · rw [ite_eq_left hab] at hα
    rw [ite_eq_right (not_lt.mpr hab.le)] at hβ
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g,?_,?_⟩
    · simpa only [hα,hβ,neg_neg] using hG
    · change (fun z:ℍ=>g • z) '' T.interior=_
      simpa only [min_eq_left hab.le,max_eq_right hab.le,hα,hβ,neg_neg] using hI
  · have hba : b.re<a.re:=lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
    rw [ite_eq_right hab] at hα
    rw [ite_eq_left hba] at hβ
    refine ⟨idealTriangleAxisMirror*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g,?_,?_⟩
    · change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g) _=_
      rw [←native_subgroupConjugate_compose,hG,normalizedIdealTriangleGroup_axis_conjugate,hα,hβ]
    · change (fun z:ℍ=>idealTriangleAxisMirror (g • z)) '' T.interior=_
      calc
        _ = idealTriangleAxisMirror '' ((fun z:ℍ=>g • z) '' T.interior) := (Set.image_image _ _ _).symm
        _ = _ := by
          rw [hI,min_eq_right hba.le,max_eq_left hba.le,idealTriangleAxisMirror_graph_image]
          rw [hα,hβ]

/-- The literal original ideal triangle is a fundamental domain for its actual three-mirror group. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_ideal_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα : IsIntegralTriangleAngle T.alpha) (hβ : IsIntegralTriangleAngle T.beta)
    (hγ : T.gamma=0) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (triangleReflectionGroup T) ℍ volume T.interior := by
  have hs : T.alpha+T.beta<Real.pi:=by simpa only [hγ,add_zero] using T.angle_sum_lt_pi
  let U:=prescribedIdealHTriangle T.alpha T.beta hα.nonneg hβ.nonneg hs
  obtain ⟨e,hG,hI⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.ideal_group_and_interior_canonical T hγ
  have hgU : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T)=triangleReflectionGroup U:=by
    rw [hG]
    exact (prescribedIdealHTriangle_reflection_eq_normalized _ _ _ _ _).symm
  have hiU : e '' T.interior=U.interior:=by
    rw [hI]
    exact (prescribedIdealHTriangle_interior_graph _ _ _ _ _).symm
  have hU:=prescribedIdealHTriangle_fundamentalDomain T.alpha T.beta hα hβ hs
  rw [←hgU] at hU
  have hh:=native_fundamentalDomain_conjugate_preimage _ e hU
  rw [←hiU,preimage_image_eq _ e.injective] at hh
  exact hh

/-- Cyclic relabelling does not alter the original open hyperbolic triangle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : T.cycle.interior=T.interior := by
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.interior
  rw [T.cycle_toDiscTriangle,T.toDiscTriangle.cycle_interior]

/-- The compact integral-angle case uses the very same original finite triangle, without a
replacement-domain hypothesis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_finite_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q r : ℕ) (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ))
    (hc : T.gamma=Real.pi/(r:ℝ)) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (triangleReflectionGroup T) ℍ volume T.interior := by
  obtain ⟨U,hU⟩:=positive_angle_closedTriangle_has_finite_model T
    (by rw [ha]; positivity) (by rw [hb]; positivity) (by rw [hc]; positivity)
  let n : Fin 3→ℕ:=![p,q,r]
  have hn : ∀i,2≤n i:=by intro i;fin_cases i <;> assumption
  have hu : ∀i,finiteTriangleVertexAngle U i=Real.pi/(n i:ℝ):=by
    intro i
    fin_cases i
    · exact (U.closed_angles.1.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.alpha hU)).trans ha
    · exact (U.closed_angles.2.1.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.beta hU)).trans hb
    · exact (U.closed_angles.2.2.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.gamma hU)).trans hc
  have h:= (finiteTriangle_integral_poincare U n hn hu).2
  rw [finiteTrianglePoincarePairing_generated,←U.interior_toClosedHTriangle,hU] at h
  exact h

/-- Every original reciprocal-integer-or-ideal triangle has its literal original interior as a
fundamental domain for its actual full reflection group. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_integral_angles
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha : IsIntegralTriangleAngle T.alpha) (hb : IsIntegralTriangleAngle T.beta)
    (hc : IsIntegralTriangleAngle T.gamma) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (triangleReflectionGroup T) ℍ volume T.interior := by
  by_cases hγ : T.gamma=0
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_ideal_integral T ha hb hγ
  by_cases hα : T.alpha=0
  · have h1:=closedHTriangle_cycle_angles T
    have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_ideal_integral T.cycle
      (h1.1.symm ▸ hb) (h1.2.1.symm ▸ hc) (h1.2.2.trans hα)
    rwa [triangleReflectionGroup_cycle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior] at hd
  by_cases hβ : T.beta=0
  · have h1:=closedHTriangle_cycle_angles T
    have h2:=closedHTriangle_cycle_angles T.cycle
    have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_ideal_integral T.cycle.cycle
      ((h2.1.trans h1.2.1).symm ▸ hc) ((h2.2.1.trans h1.2.2).symm ▸ ha)
      ((h2.2.2.trans h1.1).trans hβ)
    repeat rw [triangleReflectionGroup_cycle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior] at hd
    exact hd
  obtain ⟨p,hp,ha⟩:=ha.resolve_left hα
  obtain ⟨q,hq,hb⟩:=hb.resolve_left hβ
  obtain ⟨r,hr,hc⟩:=hc.resolve_left hγ
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_finite_integral T p q r hp hq hr ha hb hc

end LowDimensionalTopology.Geometry.Fuchsian
