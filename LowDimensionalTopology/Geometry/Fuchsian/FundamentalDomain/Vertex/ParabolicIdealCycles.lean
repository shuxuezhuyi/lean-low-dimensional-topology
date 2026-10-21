module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HorocyclicFundamentalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine positive-height horizontal horocyclic region has precisely infinity as ideal accumulation point. -/
theorem horizontalHorocyclicRegion_idealEndpoints (k : ℝ) (hk : 0 < k) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints (_root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) = {∞} := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    simp only [mem_singleton_iff,iff_true]
    refine ⟨?_,by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]⟩
    apply mem_closure_of_tendsto (vertical_probe_tendsto_infty 0)
    filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_gt_atTop k)] with t ht
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.exp t) (Real.exp_pos t),ht,rfl⟩
  | coe z =>
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints_finite_iff]
    simp only [OnePoint.coe_ne_infty,mem_singleton_iff,iff_false]
    rintro ⟨hz,hzi⟩
    have hbound : closure (((↑) : ℍ → ℂ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) ⊆ {u : ℂ | k ≤ u.im} := by
      apply closure_minimal
      · rintro _ ⟨w,hw,rfl⟩
        change k < w.im at hw
        exact hw.le
      · exact isClosed_le continuous_const Complex.continuous_im
    have hh := hbound hz
    change k ≤ z.im at hh
    linarith

/-- Genuine real determinant-one actions transport the entire actual ideal endpoint set. -/
theorem realSL_traceIdealEndpoints (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints ((fun z : ℍ => A • z) '' S) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints S := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ A
  have hg : 0 < g.val.det := by simp [g]
  have hproj : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val = _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix g) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  have hact (z : ℍ) : g • z = A • z := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    calc
      _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((z : ℂ) : OnePoint ℂ) := by
        rw [hproj]
        exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realMobiusMatrix_coe g hg z).symm
      _ = _ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_traceIdealEndpoints g hg S
  have hfunc : (fun z : ℍ => g • z) = (fun z : ℍ => A • z) := funext hact
  rw [hfunc,←hproj] at he
  exact he

/-- An actual transformed horocyclic region has exactly its genuine transformed basepoint as ideal endpoint. -/
theorem realSL_horocyclic_region_idealEndpoints (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (k : ℝ) (hk : 0 < k) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints ((fun z : ℍ => A • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) =
      {(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞} := by
  rw [realSL_traceIdealEndpoints,horizontalHorocyclicRegion_idealEndpoints k hk,image_singleton]

/-- Every genuine ray toward infinity enters every positive-height horocyclic region. -/
theorem hRay_inter_horizontal_horocyclic_nonempty
    {z : ℍ}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hR : R.idealEndpoint = ∞) (k : ℝ) (hk : 0 < k) :
    (R.val ∩ _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k).Nonempty := by
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe z.re (z.im+k+1) (by linarith [z.im_pos])
  refine ⟨w,(R.mem_iff_upward_of_endpoint_infty hR w).mpr ⟨rfl,?_⟩,?_⟩
  · change z.im ≤ z.im+k+1
    linarith
  · change k < z.im+k+1
    linarith [z.im_pos]

/-- The native real determinant-one action agrees with its actual real general-linear action. -/
theorem realSL_mapGL_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ A) • z = A • z := by
  rfl

/-- Actual real determinant-one maps carry genuine ray endpoints by the same Mobius map. -/
theorem hRay_realSLMap_idealEndpoint {z : ℍ} (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A)).idealEndpoint =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val R.idealEndpoint := by
  rw [R.realGLMap_idealEndpoint _ (by simp)]
  congr 1
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
    _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]

/-- Every genuine ray ending at a horocyclic region's actual ideal endpoint enters that region. -/
theorem hRay_inter_realSL_horocyclic_nonempty {z : ℍ} (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hR : R.idealEndpoint = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞)
    (k : ℝ)
    (hk : 0 < k) :
    (R.val ∩ ((fun w : ℍ => A • w) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).Nonempty := by
  let S := R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A⁻¹)
  have hS : S.idealEndpoint = ∞ := by
    rw [hRay_realSLMap_idealEndpoint R A⁻¹,map_inv,hR]
    exact Equiv.symm_apply_apply _ _
  obtain ⟨w,hwS,hwK⟩ := hRay_inter_horizontal_horocyclic_nonempty S hS k hk
  change w ∈ (R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A⁻¹)).val at hwS
  rw [← R.realGLMap_carrier] at hwS
  obtain ⟨u,hu,heu⟩ := hwS
  change Matrix.SpecialLinearGroup.mapGL ℝ A⁻¹ • u = w at heu
  rw [realSL_mapGL_smul] at heu
  refine ⟨u,hu,w,hwK,?_⟩
  change A • w = u
  rw [←heu,smul_inv_smul]

/-- The literal ideal-boundary cycle is the actual ideal boundary intersected with the
original whole-group boundary orbit. -/
def fuchsianPolygonIdealCycle {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (ξ : OnePoint ℂ) : Set (OnePoint ℂ) :=
  (OnePoint.some '' fuchsianPolygonIdealBoundary P D) ∩ MulAction.orbit H ξ

/-- Finitely many genuine horocyclic regions have only finitely many genuine ideal endpoints. -/
theorem finite_horocyclic_images_idealEndpoints
    (N : Subgroup Mobius.complexMobiusGroup)
    (k : ℝ) (hk : 0 < k) (F : Set (Set ℍ)) (hF : F.Finite)
    (himages : ∀ L ∈ F, ∃ g : fordNativeGroup N,
      L = (g.val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) :
    (⋃ L ∈ F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints L).Finite := by
  apply hF.biUnion
  intro L hL
  obtain ⟨g,rfl⟩ := himages L hL
  obtain ⟨B,_hB,hBg⟩ := (mem_fordNativeGroup N g.val).mp g.property
  have hact : (fun z : ℍ => B • z) = g.val := congrArg (fun e : ℍ ≃ᵢ ℍ => (e : ℍ → ℍ)) hBg
  rw [←hact,realSL_horocyclic_region_idealEndpoints B k hk]
  exact finite_singleton _

/-- The actual cycle of every parabolic ideal point in any genuine convex locally finite
fundamental polygon is finite, with no finite-side or finite-generation assumption. -/
theorem IsConvexFuchsianPolygon.parabolic_idealCycle_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) :
    (fuchsianPolygonIdealCycle P D ξ).Finite := by
  obtain ⟨q,hq,hT,hqξ⟩ := parabolic_unit_halfPlane_normalizer P f hf ξ hfix
  obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let S := fordSLNativeHom A '' (P.halfPlaneCoordinate '' D)
  let F : Set (Set ℍ) := {L | ∃ g : fordNativeGroup N,
    L = (g.val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧ (closure S ∩ L).Nonempty}
  have hF : F.Finite := hD.locallyFinite.normalized_horocyclic_images_finite q hq A hA hT 1 zero_lt_one
  have hU := finite_horocyclic_images_idealEndpoints N 1 zero_lt_one F hF
    (fun L hL => by obtain ⟨g,hg,_⟩ := hL; exact ⟨g,hg⟩)
  apply (hU.preimage q.val.injective.injOn).subset
  rintro _ ⟨⟨η,hη,rfl⟩,hηorbit⟩
  obtain ⟨g,hgη⟩ := MulAction.mem_orbit_iff.mp hηorbit
  have hpres : (q*g.val*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [←hq,_root_.LowDimensionalTopology.Geometry.Surfaces.cusp_conjugate_image,P.image_eq g]
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  let e : fordNativeGroup N := ⟨fordSLNativeHom B,(mem_fordNativeGroup N _).mpr
    ⟨B,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,hB.symm⟩,rfl⟩⟩
  have hBend : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ = q.val (η : OnePoint ℂ) := by
    rw [hB]
    change q.val (g.val.val (q.val.symm ∞)) = q.val (η : OnePoint ℂ)
    rw [←hqξ,Equiv.symm_apply_apply]
    exact congrArg q.val hgη
  obtain ⟨z,hz⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hηB : (η : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary η).mpr ((mem_fuchsianPolygonIdealBoundary P D η).mp hη).2
  have hηH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (η : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealBoundary_cayley_iff _).mpr (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply] using hηB)
  have hRay := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay (P.finiteCoordinate z) η hηB).toHalfPlane
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (P.halfPlaneCoordinate z) :=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (P.finiteCoordinate z) η,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm η,hηH,hRay⟩
  let R' := R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A)
  have hRend : R'.idealEndpoint = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ := by
    rw [hRay_realSLMap_idealEndpoint R A,R.idealEndpoint_unique hRay,hBend,hA]
    change q.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (η : OnePoint ℂ))) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply]
  have hRsub : R'.val ⊆ S := by
    rw [←R.realGLMap_carrier]
    have hfun : (fun w : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ A • w) = fordSLNativeHom A :=
      funext (realSL_mapGL_smul A)
    rw [hfun]
    exact image_mono (hD.ideal_halfPlane_ray_subset z hz η hη)
  obtain ⟨w,hwR,hwL⟩ := hRay_inter_realSL_horocyclic_nonempty R' B hRend 1 zero_lt_one
  let L := (fun w : ℍ => B • w) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1
  have hLF : L ∈ F := ⟨e,rfl,w,subset_closure (hRsub hwR),hwL⟩
  apply mem_iUnion.mpr
  refine ⟨L,mem_iUnion.mpr ⟨hLF,?_⟩⟩
  change q.val (η : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints L
  rw [realSL_horocyclic_region_idealEndpoints B 1 zero_lt_one,hBend]
  exact mem_singleton _

end LowDimensionalTopology.Geometry.Fuchsian
