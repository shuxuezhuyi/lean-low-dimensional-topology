/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.PeriodicSideOrbitSets
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshStraightAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.UnitDiscCrossing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FuchsianSideConnectors
/-!
# Actual hyperbolic side-pairing necessity

Compact connected connectors in a genuine convex fundamental polygon yield periodic traces.
Their actual ideal endpoints, round-disc crosscuts, and disjoint cyclic-coset translates imply
simplicity of the entire hyperbolic axis. Combined with the full-stabilizer construction, this
proves that a primitive hyperbolic element pairs sides exactly when it is simple,
and gives the side-pairing classification.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology OnePoint Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual Poincare-disc point in the standard real two-plane, with no boundary point removed. -/
def halfPlaneDiscPlane (z : ℍ) : EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z :
    Complex.UnitDisc):ℂ)

theorem halfPlaneDiscPlane_isOpenEmbedding : Topology.IsOpenEmbedding halfPlaneDiscPlane := by
  exact Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenEmbedding.comp
    (_root_.LowDimensionalTopology.Geometry.Polygon.unitDisc_coe_isOpenEmbedding.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenEmbedding)

theorem halfPlaneDiscPlane_range : range halfPlaneDiscPlane = ball 0 1 := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    rw [mem_ball_zero_iff,halfPlaneDiscPlane,Complex.orthonormalBasisOneI.repr.norm_map]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z).norm_lt_one
  · intro hx
    have hn : ‖Complex.orthonormalBasisOneI.repr.symm x‖ < 1 := by
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
      exact mem_ball_zero_iff.mp hx
    let d : Complex.UnitDisc := Complex.UnitDisc.mk _ hn
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d,?_⟩
    change Complex.orthonormalBasisOneI.repr ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d) : Complex.UnitDisc):ℂ) = x
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply x

/-- This plane chart is exactly the actual compactified Cayley transformation at every native point. -/
theorem halfPlaneDiscPlane_boundary (z : ℍ) :
    ((Complex.orthonormalBasisOneI.repr.symm (halfPlaneDiscPlane z) : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) := by
  rw [halfPlaneDiscPlane,Complex.orthonormalBasisOneI.repr.symm_apply_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply]
  change _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane z).symm

/-- The true closed periodic trace stays closed relative to the whole actual open unit ball. -/
theorem halfPlaneDiscPlane_closure_inter_ball {S : Set ℍ} (hS : IsClosed S) :
    closure (halfPlaneDiscPlane '' S) ∩ ball 0 1 = halfPlaneDiscPlane '' S := by
  apply Subset.antisymm
  · rintro x ⟨hx,hxb⟩
    obtain ⟨z,rfl⟩ := halfPlaneDiscPlane_range ▸ hxb
    have hz : z ∈ closure S := by
      rwa [halfPlaneDiscPlane_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image S]
    exact mem_image_of_mem _ (hS.closure_subset hz)
  · rintro x ⟨z,hz,rfl⟩
    exact ⟨subset_closure (mem_image_of_mem _ hz),halfPlaneDiscPlane_range ▸ mem_range_self z⟩

/-- The inverse compactified Cayley coordinate is a genuine everywhere-continuous map on the finite real plane. -/
def planeToHalfPlaneSphere (x : EuclideanSpace ℝ (Fin
  2)) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (((Complex.orthonormalBasisOneI.repr.symm x : ℂ)
    : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

theorem planeToHalfPlaneSphere_continuous : Continuous planeToHalfPlaneSphere :=
  (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹).comp
    (OnePoint.continuous_coe.comp Complex.orthonormalBasisOneI.repr.symm.continuous)

theorem planeToHalfPlaneSphere_chart (z : ℍ) :
    planeToHalfPlaneSphere (halfPlaneDiscPlane z) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z := by
  unfold planeToHalfPlaneSphere
  rw [halfPlaneDiscPlane_boundary]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply _

/-- Actual points of the round ideal sphere map into the genuine extended real axis. -/
theorem planeToHalfPlaneSphere_unitSphere {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ sphere 0 1) : planeToHalfPlaneSphere x ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
  have hnorm : ‖Complex.orthonormalBasisOneI.repr.symm x‖ = 1 := by
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp hx
  have hc : ((Complex.orthonormalBasisOneI.repr.symm x : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero]
    exact hnorm
  have him : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis = _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
    exact congrArg Subtype.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_image_boundary
  rw [←him] at hc
  obtain ⟨y,hy,he⟩ := hc
  unfold planeToHalfPlaneSphere
  rw [←he]
  have hcan : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val y) = y := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply y
  rw [hcan]
  exact hy


/-- The finite real plane embeds into the genuine compactified complex sphere. -/
def planeComplexSphere (x : EuclideanSpace ℝ (Fin 2)) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  ((Complex.orthonormalBasisOneI.repr.symm x : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)

theorem planeComplexSphere_isOpenEmbedding : Topology.IsOpenEmbedding planeComplexSphere :=
  OnePoint.isOpenEmbedding_coe.comp Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.isOpenEmbedding

theorem planeComplexSphere_chart_image (S : Set ℍ) :
    planeComplexSphere '' (halfPlaneDiscPlane '' S) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) := by
  rw [image_image,image_image]
  exact image_congr (fun z _hz => halfPlaneDiscPlane_boundary z)

theorem planeToHalfPlaneSphere_chart_image (S : Set ℍ) :
    planeToHalfPlaneSphere '' (halfPlaneDiscPlane '' S) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S := by
  rw [image_image]
  exact image_congr (fun z _hz => planeToHalfPlaneSphere_chart z)

theorem cayley_zero_eq_neg_one : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((-1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_coe 0 (by simp)]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula]

/-- The real-plane periodic trace has no ideal accumulation other than the two actual diameter endpoints. -/
theorem HalfPlaneFuchsianGroup.dilation_plane_trace_boundary_subset {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈
      H)
    {C : Set ℍ} (hC : IsCompact C) :
    letI := P.nativeAction
    closure (halfPlaneDiscPlane '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l,hfH⟩ : H) C) ∩ sphere 0 1 ⊆
      {Complex.orthonormalBasisOneI.repr (-1),Complex.orthonormalBasisOneI.repr 1} := by
  let nativePlaneTraceBoundaryAction := P.nativeAction
  rintro x ⟨hx,hxs⟩
  have hF : planeToHalfPlaneSphere x ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
    rw [←planeToHalfPlaneSphere_chart_image]
    exact image_closure_subset_closure_image planeToHalfPlaneSphere_continuous (mem_image_of_mem _ hx)
  have hb := P.dilation_connector_trace_boundary l hfH hC _ hF (planeToHalfPlaneSphere_unitSphere hxs)
  have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (planeToHalfPlaneSphere
    x) = planeComplexSphere x :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.apply_symm_apply _
  rcases hb with hz | hz
  · have he : planeComplexSphere x = ((-1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := hq.symm.trans (by rw [hz,cayley_zero_eq_neg_one])
    have hcomplex : Complex.orthonormalBasisOneI.repr.symm x = -1 := OnePoint.coe_injective he
    exact Or.inl ((Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
      Complex.orthonormalBasisOneI.repr hcomplex))
  · have he : planeComplexSphere x = ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := hq.symm.trans (by rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty])
    have hcomplex : Complex.orthonormalBasisOneI.repr.symm x = 1 := OnePoint.coe_injective he
    exact Or.inr ((Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
      Complex.orthonormalBasisOneI.repr hcomplex))

/-- A true compactified endpoint of a native trace remains a limiting endpoint in the actual finite real plane. -/
theorem halfPlaneDiscPlane_endpoint_mem_closure {S : Set ℍ} {a :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (ha : a ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)) {b : ℂ}
    (hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val a =
      (b:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    Complex.orthonormalBasisOneI.repr b ∈ closure (halfPlaneDiscPlane '' S) := by
  have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val a ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)) :=
    image_closure_subset_closure_image (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (mem_image_of_mem _ ha)
  rw [hb,←planeComplexSphere_chart_image] at h
  rw [planeComplexSphere_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
  simpa only [mem_preimage,planeComplexSphere,Complex.orthonormalBasisOneI.repr.symm_apply_apply] using h

/-- The actual compactified periodic trace meets the round ideal sphere in exactly the two diameter endpoints. -/
theorem HalfPlaneFuchsianGroup.dilation_plane_trace_ideal_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hC : IsCompact C) (hne : C.Nonempty) :
    letI := P.nativeAction
    closure (halfPlaneDiscPlane '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l,hfH⟩ : H) C) ∩ sphere 0 1 =
      {Complex.orthonormalBasisOneI.repr (-1),Complex.orthonormalBasisOneI.repr 1} := by
  let nativePlaneTraceIdealBoundaryAction := P.nativeAction
  apply Subset.antisymm (P.dilation_plane_trace_boundary_subset l hfH hC)
  rintro x (rfl | rfl)
  · refine ⟨halfPlaneDiscPlane_endpoint_mem_closure (P.dilation_trace_zero_mem_closure l hl hfH hne)
    cayley_zero_eq_neg_one,?_⟩
    rw [mem_sphere_zero_iff_norm,Complex.orthonormalBasisOneI.repr.norm_map]
    norm_num
  · refine ⟨halfPlaneDiscPlane_endpoint_mem_closure (P.dilation_trace_infty_mem_closure l hl hfH hne) ?_,?_⟩
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty]
    · rw [mem_sphere_zero_iff_norm,Complex.orthonormalBasisOneI.repr.norm_map]
      norm_num

end LowDimensionalTopology.Geometry.Fuchsian

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric Schoenflies
open scoped Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing

/-- A literal upper or lower closed half of the round unit circle. -/
def signedUnitSemicircle (s : ℝ) : Set Plane :=
  sphere 0 1 ∩ {z | 0 ≤ s * (Complex.orthonormalBasisOneI.repr.symm z).im}

/-- The graph parametrization retains both actual diameter endpoints. -/
def signedSemicircleParam (s t : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr
    (((2*t-1 : ℝ):ℂ) + ((s * Real.sqrt (1-(2*t-1)^2) : ℝ):ℂ)*Complex.I)

theorem signedSemicircleParam_continuous (s : ℝ) : Continuous (signedSemicircleParam s) := by
  unfold signedSemicircleParam
  fun_prop

theorem signedSemicircleParam_injOn (s : ℝ) :
    InjOn (signedSemicircleParam s) unitInterval := by
  intro a _ha b _hb hab
  have he := congrArg Complex.re (Complex.orthonormalBasisOneI.repr.injective hab)
  simp only [Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at he
  linarith

theorem signedSemicircleParam_image (s : ℝ) (hs : s^2=1) :
    signedSemicircleParam s '' unitInterval = signedUnitSemicircle s := by
  apply Subset.antisymm
  · rintro x ⟨t,ht,rfl⟩
    have hnon : 0 ≤ 1-(2*t-1)^2 := by
      rcases ht with ⟨ht0,ht1⟩
      nlinarith [sq_nonneg t, sq_nonneg (1-t)]
    have hsqrt := Real.sq_sqrt hnon
    have hn : ‖((2*t-1 : ℝ):ℂ) + ((s * Real.sqrt (1-(2*t-1)^2) : ℝ):ℂ)*Complex.I‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1:ℝ))).mp
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,add_zero,zero_add,mul_one]
      nlinarith [mul_self_nonneg (Real.sqrt (1-(2*t-1)^2))]
    refine ⟨?_,?_⟩
    · rw [mem_sphere_zero_iff_norm,signedSemicircleParam,Complex.orthonormalBasisOneI.repr.norm_map]
      exact hn
    · change 0 ≤ s * (Complex.orthonormalBasisOneI.repr.symm (signedSemicircleParam s t)).im
      simp only [signedSemicircleParam,Complex.orthonormalBasisOneI.repr.symm_apply_apply,
        Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
        Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
      nlinarith [Real.sqrt_nonneg (1-(2*t-1)^2)]
  · intro x hx
    let z := Complex.orthonormalBasisOneI.repr.symm x
    have hn : ‖z‖=1 := by
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx.1
    have hsq : z.re^2+z.im^2=1 := by
      have hh := Complex.sq_norm z
      rw [hn,Complex.normSq_apply] at hh
      nlinarith
    have hzle : -1 ≤ z.re ∧ z.re ≤ 1 := by constructor <;> nlinarith [sq_nonneg z.im]
    have hnon : 0 ≤ 1-z.re^2 := by nlinarith [sq_nonneg z.im]
    have hroot := Real.sq_sqrt hnon
    have hsim : s * Real.sqrt (1-z.re^2) = z.im := by
      have hsign : 0 ≤ s*z.im := hx.2
      have hrootpos := Real.sqrt_nonneg (1-z.re^2)
      rcases sq_eq_one_iff.mp hs with rfl | rfl <;> simp only [one_mul,neg_one_mul] at hsign ⊢ <;> nlinarith
    refine ⟨(z.re+1)/2,?_,?_⟩
    · constructor <;> linarith [hzle.1,hzle.2]
    · have hre : 2*((z.re+1)/2)-1=z.re := by ring
      rw [signedSemicircleParam,hre,hsim]
      apply Complex.orthonormalBasisOneI.repr.symm.injective
      simp only [Complex.orthonormalBasisOneI.repr.symm_apply_apply]
      exact Complex.ext (by simp [z]) (by simp [z])

theorem signedUnitSemicircle_isArc (s : ℝ) (hs : s^2=1) :
    IsArcBetween (signedUnitSemicircle s)
      (Complex.orthonormalBasisOneI.repr (-1)) (Complex.orthonormalBasisOneI.repr 1) := by
  refine ⟨signedSemicircleParam s,(signedSemicircleParam_continuous s).continuousOn,
    signedSemicircleParam_injOn s,signedSemicircleParam_image s hs,?_,?_⟩
  · norm_num [signedSemicircleParam]
  · norm_num [signedSemicircleParam]

/-- The actual two semicircles cut the round ideal circle at the actual diameter endpoints. -/
theorem unitSphere_semicircle_cutPair :
    IsCutPair (sphere (0:Plane) 1)
      (Complex.orthonormalBasisOneI.repr (-1)) (Complex.orthonormalBasisOneI.repr 1)
      (signedUnitSemicircle 1) (signedUnitSemicircle (-1)) := by
  refine ⟨signedUnitSemicircle_isArc 1 (by norm_num),
    signedUnitSemicircle_isArc (-1) (by norm_num),?_,?_⟩
  · ext x
    simp only [signedUnitSemicircle,mem_union,mem_inter_iff,mem_ofPred_eq,one_mul,neg_one_mul]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases le_total 0 (Complex.orthonormalBasisOneI.repr.symm x).im with h | h
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr ⟨hx,by linarith⟩
  · ext x
    constructor
    · rintro ⟨⟨hx,hpos⟩,⟨_hx,hneg⟩⟩
      let z := Complex.orthonormalBasisOneI.repr.symm x
      have him : z.im=0 := by change 0 ≤ 1*z.im at hpos;change 0 ≤ -1*z.im at hneg;linarith
      have hn : ‖z‖=1 := by
        rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
        exact mem_sphere_zero_iff_norm.mp hx
      have hre : z.re^2=1 := by
        have hh := Complex.sq_norm z
        rw [hn,Complex.normSq_apply,him] at hh
        nlinarith
      rcases sq_eq_one_iff.mp hre with hr | hr
      · right
        have hz : z=(1:ℂ) := Complex.ext (by simpa using hr) (by simpa using him)
        exact (Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
          Complex.orthonormalBasisOneI.repr hz)
      · left
        have hz : z=(-1:ℂ) := Complex.ext (by simpa using hr) (by simpa using him)
        exact (Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
          Complex.orthonormalBasisOneI.repr hz)
    · rintro (rfl | rfl) <;>
        simp [signedUnitSemicircle,Complex.orthonormalBasisOneI.repr.norm_map]

/-- Opposite genuine imaginary signs are enough to force intersection of connected traces. -/
theorem opposite_semicircle_traces_intersect {A B : Set Plane} {c d : Plane}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAball : A ⊆ ball 0 1) (hBball : B ⊆ ball 0 1)
    (ha : Complex.orthonormalBasisOneI.repr (-1) ∈ closure A)
    (hb : Complex.orthonormalBasisOneI.repr 1 ∈ closure A)
    (hc : c ∈ closure B) (hd : d ∈ closure B)
    (hcs : c ∈ sphere 0 1) (hds : d ∈ sphere 0 1)
    (hcpos : 0 < (Complex.orthonormalBasisOneI.repr.symm c).im)
    (hdneg : (Complex.orthonormalBasisOneI.repr.symm d).im < 0) :
    (closure A ∩ closure B).Nonempty := by
  apply alternating_ball_traces_closures_intersect hA hB hAball hBball ha hb
    unitSphere_semicircle_cutPair hc hd
  · exact ⟨hcs,by simpa using hcpos.le⟩
  · intro hh
    have hh' := hh.2
    change 0 ≤ -1*(Complex.orthonormalBasisOneI.repr.symm c).im at hh'
    linarith
  · exact ⟨hds,by change 0 ≤ -1*(Complex.orthonormalBasisOneI.repr.symm d).im;linarith⟩
  · intro hh
    have hh' := hh.2
    change 0 ≤ 1*(Complex.orthonormalBasisOneI.repr.symm d).im at hh'
    linarith

end LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped Topology Pointwise OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Reversing the generator leaves the full actual integer trace unchanged. -/
theorem cyclicOrbitTrace_inv {G X : Type*} [Group G] [MulAction G X] (g : G) (C : Set X) :
    cyclicOrbitTrace g⁻¹ C = cyclicOrbitTrace g C := by
  apply Subset.antisymm
  · rintro z hz
    obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨-n,x,hx,?_⟩
    rw [inv_zpow,zpow_neg]
  · rintro z hz
    obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨-n,x,hx,?_⟩
    rw [inv_zpow,zpow_neg,inv_inv]

/-- An actual equivariant map sends the entire integer trace onto the entire transported trace. -/
theorem cyclicOrbitTrace_image_equivariant {G K X Y : Type*} [Group G] [Group K]
    [MulAction G X] [MulAction K Y] (e : G →* K) (f : X → Y)
    (he : ∀ g x, f (g • x) = e g • f x) (g : G) (C : Set X) :
    f '' cyclicOrbitTrace g C = cyclicOrbitTrace (e g) (f '' C) := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨n,z,hz,rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,f z,mem_image_of_mem _ hz,by rw [he,map_zpow]⟩
  · rintro y hy
    obtain ⟨n,z,⟨x,hx,rfl⟩,rfl⟩ := mem_iUnion.mp hy
    refine ⟨g^n • x,mem_iUnion.mpr ⟨n,x,hx,rfl⟩,?_⟩
    rw [he,map_zpow]

/-- Whole-group equivariance transports the precise cyclic-subgroup exclusion. -/
theorem MulEquiv.mem_zpowers_iff_preimage {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (g h : G) : e h ∈ Subgroup.zpowers (e g) ↔ h ∈ Subgroup.zpowers g := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,e.injective (by rw [map_zpow];exact hn)⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,by rw [←map_zpow,hn]⟩

/-- The original side supplies a compact connected native connector with disjoint full traces outside its cyclic stabilizer. -/
theorem HalfPlaneFuchsianGroup.dilation_side_connector
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0 < l) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {D : Set P.cayleyData.domain.carrier} (hD : IsConvexFuchsianPolygon P.cayleyData D)
    (s : FuchsianPolygonSides P.cayleyData D)
    (hs : (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius *
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹) :
    letI := P.nativeAction
    ∃ w : ℍ, ∃ C : Set ℍ, IsCompact C ∧ IsPreconnected C ∧ w ∈ C ∧
      (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) • w ∈ C ∧
      ∀ h : H, h ∉ Subgroup.zpowers (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) →
        Disjoint (cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C)
          ((h • ·) '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
  let nativeSideConnectorAction := P.nativeAction
  let f : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  let F := P.cayleyCoordinate
  have he (a : H) (z : ℍ) : F (a • z) = e a • F z := P.cayleyCoordinate_equivariant a z
  have hside : fuchsianSideElement hD s = e f := Subtype.ext hs
  have hhyper : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD s).val := by
    rw [hs]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl)
  obtain ⟨v,_hvs,B,hBc,hBp,hvB,hfvB,_hBsub,_hfree,hpack⟩ := hD.hyperbolic_side_compact_connector s hhyper
  rw [hside] at hfvB hpack
  let C := F.symm '' B
  let w := F.symm ((e f)⁻¹ • v)
  have hback (a : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H) (z : P.cayleyData.domain.carrier) :
      F.symm (a • z) = e.symm a • F.symm z := by
    apply F.injective
    rw [F.apply_symm_apply,he,e.apply_symm_apply,F.apply_symm_apply]
  have htrace : F '' cyclicOrbitTrace f C = cyclicOrbitTrace (e f) B := by
    rw [cyclicOrbitTrace_image_equivariant e.toMonoidHom F he]
    have him : F '' C = B := F.toEquiv.image_symm_image B
    rw [him]
    rfl
  refine ⟨w,C,hBc.image F.symm.continuous,hBp.image _ F.symm.continuous.continuousOn,
    mem_image_of_mem _ hfvB,?_,?_⟩
  · have hf : f • w = F.symm v := by
      apply F.injective
      rw [he,F.apply_symm_apply,F.apply_symm_apply]
      exact smul_inv_smul _ _
    rw [hf]
    exact mem_image_of_mem _ hvB
  · intro h hh
    have hnot : e h ∉ Subgroup.zpowers (e
      f) := fun hmem => hh ((_root_.LowDimensionalTopology.Geometry.Fuchsian.MulEquiv.mem_zpowers_iff_preimage e f h).mp
      hmem)
    have hdis := hpack (e h) hnot
    change Disjoint (cyclicOrbitTrace (e f)⁻¹ B) ((e h • ·) '' cyclicOrbitTrace (e f)⁻¹ B) at hdis
    rw [cyclicOrbitTrace_inv] at hdis
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y,hy,rfl⟩
    apply Set.disjoint_left.mp hdis
    · rw [←htrace]
      exact mem_image_of_mem _ hz
    · exact ⟨F y,by rw [←htrace];exact mem_image_of_mem _ hy,(he h y).symm⟩

end LowDimensionalTopology.Geometry.Fuchsian

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual image of a point on the imaginary axis has the literal real fractional coordinate. -/
theorem axisSL_image_re (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (y : ℝ) (hy : 0 < y) :
    (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy).re =
      (A 0 0*A 1 0*y^2+A 0 1*A 1 1)/((A 1 0)^2*y^2+(A 1 1)^2) := by
  change ((A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy : ℍ):ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply,Complex.div_re,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  simp [Complex.normSq_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  ring

/-- The real denominator is strictly positive at every actual imaginary-axis point. -/
theorem axisSL_denominator_pos (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (y : ℝ) (hy : 0 < y) :
    0 < (A 1 0)^2*y^2+(A 1 1)^2 := by
  by_cases hc : A 1 0 = 0
  · have hd : A 1 1 ≠ 0 := by
      intro hd
      have hdet := A.det_coe
      rw [Matrix.det_fin_two,hc,hd] at hdet
      norm_num at hdet
    simpa only [hc,zero_pow (by norm_num : 2≠0),zero_mul,zero_add] using sq_pos_of_ne_zero hd
  · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos hy)) (sq_nonneg _)

/-- Vanishing of both coefficient products preserves the whole actual imaginary axis. -/
theorem axisSL_image_axis_of_products_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hac : A 0 0*A 1 0=0) (hbd : A 0 1*A 1 1=0) :
    (A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  have hmap (z : ℍ) (hz : z ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) :
      A • z ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    have he : z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 z.im z.im_pos := UpperHalfPlane.ext (Complex.ext hz rfl)
    rw [he]
    change (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 z.im z.im_pos).re=0
    rw [axisSL_image_re,hac,hbd,zero_mul,zero_add,zero_div]
  let g := Matrix.SpecialLinearGroup.mapGL ℝ A
  let L := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap g
  have hcarrier : L.carrier=(A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap_carrier g
  obtain ⟨z,w,hz,hw,hzw⟩ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).exists_two_points
  have he : L=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
    apply L.eq_of_two_points _ ((isometry_smul ℍ A).injective.ne hzw)
    · rw [hcarrier];exact mem_image_of_mem _ hz
    · rw [hcarrier];exact mem_image_of_mem _ hw
    · exact hmap z hz
    · exact hmap w hw
  rw [←hcarrier,he]

/-- A genuine transverse intersection has strictly alternating real ideal endpoint signs. -/
theorem axisSL_crossing_product_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hne : (A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier ≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)
    {p : ℍ} (hp : p ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)
    (hAp : A • p ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) :
    (A 0 0*A 1 0)*(A 0 1*A 1 1) < 0 := by
  have he : p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 p.im p.im_pos := UpperHalfPlane.ext (Complex.ext hp rfl)
  change (A • p).re=0 at hAp
  have hzero : A 0 0*A 1 0*p.im^2+A 0 1*A 1 1=0 := by
    have hr : (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 p.im p.im_pos).re=0 := by simpa only [←he] using hAp
    rw [axisSL_image_re] at hr
    exact (div_eq_zero_iff.mp hr).resolve_right (ne_of_gt (axisSL_denominator_pos A p.im p.im_pos))
  have hac : A 0 0*A 1 0 ≠ 0 := by
    intro hac
    have hbd : A 0 1*A 1 1=0 := by simpa only [hac,zero_mul,zero_add] using hzero
    exact hne (axisSL_image_axis_of_products_zero A hac hbd)
  have hfac : 0 < (A 0 0*A 1 0)^2*p.im^2 := mul_pos (sq_pos_of_ne_zero hac) (sq_pos_of_pos p.im_pos)
  have hmul := congrArg (fun t : ℝ => (A 0 0*A 1 0)*t) hzero
  nlinarith [hmul]

/-- The actual finite image of zero, with no arbitrary matrix representative. -/
theorem axisSL_real_zero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hd : A 1 1≠0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(((A 0 1/A 1 1:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
  change (if (A 1 0:ℂ)*0+(A 1 1:ℂ)=0 then ∞ else
    ((((A 0 0:ℂ)*0+(A 0 1:ℂ))/((A 1 0:ℂ)*0+(A 1
      1:ℂ)):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = _
  simp only [mul_zero,zero_add,Complex.ofReal_ne_zero.mpr hd,ite_false,Complex.ofReal_div]

/-- The genuine boundary Cayley transform has an explicit imaginary part on every real point. -/
theorem cayley_real_im (x : ℝ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (x:ℂ)).im = -2*x/(x^2+1) := by
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula,Complex.div_im,Complex.normSq_apply]
  ring

/-- Actual real boundary points become true round-circle points. -/
theorem cayley_real_norm (x : ℝ) : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (x:ℂ)‖ = 1 := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_norm_eq_one_iff (x:ℂ) ?_).mpr
  · exact Complex.ofReal_im _
  · intro h
    have hh := congrArg Complex.im h
    norm_num at hh

/-- Opposite real signs become opposite true semicircle signs. -/
theorem cayley_real_im_product_neg {x y : ℝ} (hxy : x*y < 0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (x:ℂ)).im*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (y:ℂ)).im < 0 := by
  rw [cayley_real_im,cayley_real_im,div_mul_div_comm]
  apply div_neg_of_neg_of_pos
  · nlinarith
  · exact mul_pos (by positivity) (by positivity)

end LowDimensionalTopology.Geometry.Fuchsian

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Whole real Mobius maps take the actual completed trace boundary to its actual endpoint images. -/
theorem realSL_translated_trace_boundary_subset (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {S : Set ℍ}
    (hS : closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) ∩
      _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ⊆
      {((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞})
    {x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hx : x ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((A • · : ℍ→ℍ) '' S)))
    (hxR : x ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis) :
    x ∈ ({(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have himg : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((A • · : ℍ→ℍ) '' S) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) := by
    rw [image_image,image_image]
    exact image_congr (fun z _hz => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z).symm)
  rw [himg] at hx
  change x ∈ closure ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) ''
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)) at hx
  rw [←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)).image_closure] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have hyR : y ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
    have hm := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_maps_boundary A⁻¹
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis] at hm
    have hh := hm hxR
    rw [map_inv] at hh
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val.symm_apply_apply y ▸ hh
  rcases hS ⟨hy,hyR⟩ with hz | hz
  · exact Or.inl (congrArg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val hz)
  · exact Or.inr (congrArg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val hz)

/-- Every actual translated endpoint remains in the completed native trace closure. -/
theorem realSL_trace_endpoint_mem_closure (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {S : Set ℍ} {x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hx : x ∈ closure
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val x ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((A • · : ℍ→ℍ) '' S)) := by
  have hh := image_closure_subset_closure_image (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (mem_image_of_mem _ hx)
  have himg : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A).val '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((A • · : ℍ→ℍ) '' S) := by
    rw [image_image,image_image]
    exact image_congr (fun z _hz => _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z)
  rwa [himg] at hh

/-- Boundary Cayley evaluation on every real point is finite and literal. -/
theorem cayley_real_boundary (x : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (((x:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (x:ℂ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_coe]
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

/-- A closed native trace and a disjoint closed translate have disjoint finite-plane closures whenever their actual ideal endpoints are all distinct. -/
theorem disjoint_plane_trace_closures {S T : Set ℍ}
    (hS : IsClosed S) (hT : IsClosed T) (hdis : Disjoint S T)
    (hboundary : Disjoint
      (closure (halfPlaneDiscPlane '' S) ∩ sphere 0 1)
      (closure (halfPlaneDiscPlane '' T) ∩ sphere 0 1)) :
    Disjoint (closure (halfPlaneDiscPlane '' S)) (closure (halfPlaneDiscPlane '' T)) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hzcb : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    have hsub : halfPlaneDiscPlane '' S ⊆ ball 0 1 := by
      rintro x ⟨z,_hz,rfl⟩
      rw [←halfPlaneDiscPlane_range]
      exact mem_range_self z
    have hcl := closure_mono hsub hzS
    rwa [closure_ball (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num : (1:ℝ)≠0)] at hcl
  by_cases hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  · have hs : z ∈ halfPlaneDiscPlane '' S := by
      rw [←halfPlaneDiscPlane_closure_inter_ball hS]
      exact ⟨hzS,hz⟩
    have ht : z ∈ halfPlaneDiscPlane '' T := by
      rw [←halfPlaneDiscPlane_closure_inter_ball hT]
      exact ⟨hzT,hz⟩
    exact Set.disjoint_left.mp ((Set.disjoint_image_iff halfPlaneDiscPlane_isOpenEmbedding.injective).mpr hdis) hs ht
  · have hzs : z ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have hn := mem_closedBall_zero_iff.mp hzcb
      have hnn : ¬‖z‖<1 := fun hh => hz (mem_ball_zero_iff.mpr hh)
      exact le_antisymm hn (le_of_not_gt hnn)
    exact Set.disjoint_left.mp hboundary ⟨hzS,hzs⟩ ⟨hzT,hzs⟩

/-- Any genuine two-point ideal boundary becomes the corresponding actual two points on the round circle. -/
theorem plane_trace_boundary_subset_of_native {S : Set ℍ} {a b :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hS : closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) ∩
      _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ⊆ ({a,b} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    {c d : ℂ} (hca : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
      a=(c:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hcb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
      b=(d:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    closure (halfPlaneDiscPlane '' S) ∩ sphere 0 1 ⊆
      {Complex.orthonormalBasisOneI.repr c,Complex.orthonormalBasisOneI.repr d} := by
  rintro x ⟨hx,hxs⟩
  have hF : planeToHalfPlaneSphere x ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) := by
    rw [←planeToHalfPlaneSphere_chart_image]
    exact image_closure_subset_closure_image planeToHalfPlaneSphere_continuous (mem_image_of_mem _ hx)
  have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (planeToHalfPlaneSphere
    x)=planeComplexSphere x :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.apply_symm_apply _
  rcases hS ⟨hF,planeToHalfPlaneSphere_unitSphere hxs⟩ with ha | hb
  · have he : planeComplexSphere x=(c:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := hq.symm.trans (by rw [ha,hca])
    have hc : Complex.orthonormalBasisOneI.repr.symm x=c := OnePoint.coe_injective he
    exact Or.inl ((Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
      Complex.orthonormalBasisOneI.repr hc))
  · have he : planeComplexSphere x=(d:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := hq.symm.trans (by rw [hb,hcb])
    have hd : Complex.orthonormalBasisOneI.repr.symm x=d := OnePoint.coe_injective he
    exact Or.inr ((Complex.orthonormalBasisOneI.repr.apply_symm_apply x).symm.trans (congrArg
      Complex.orthonormalBasisOneI.repr hd))

/-- A transverse axis translate forces the genuine periodic traces to meet, without any polygonality or simplicity assumption on the traces. -/
theorem realSL_crossing_traces_intersect {S : Set ℍ}
    (hSc : IsClosed S) (hSp : IsPreconnected S)
    (hzero : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ closure
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S))
    (hinfty : (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ closure
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S))
    (hSboundary : closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) ∩
      _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ⊆
      ({((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hprod : (A 0 0*A 1 0)*(A 0 1*A 1 1)<0) :
    (S ∩ ((A • · : ℍ→ℍ) '' S)).Nonempty := by
  have ha : A 0 0≠0 := by intro he;rw [he] at hprod;norm_num at hprod
  have hb : A 0 1≠0 := by intro he;rw [he] at hprod;norm_num at hprod
  have hc : A 1 0≠0 := by intro he;rw [he] at hprod;norm_num at hprod
  have hd : A 1 1≠0 := by intro he;rw [he] at hprod;norm_num at hprod
  let x : ℝ := A 0 1/A 1 1
  let y : ℝ := A 0 0/A 1 0
  let c : ℂ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (x:ℂ)
  let d : ℂ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula (y:ℂ)
  have hxy : x*y<0 := by
    have he : x*y=(A 0 0*A 1 0)*(A 0 1*A 1 1)/(A 1 0*A 1 1)^2 := by
      dsimp only [x,y]
      field_simp
    rw [he]
    exact div_neg_of_neg_of_pos hprod (sq_pos_of_ne_zero (mul_ne_zero hc hd))
  have himprod : c.im*d.im<0 := cayley_real_im_product_neg hxy
  have hci : c.im≠0 := by intro he;rw [he,zero_mul] at himprod;linarith
  have hdi : d.im≠0 := by intro he;rw [he,mul_zero] at himprod;linarith
  have hA0 : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := axisSL_real_zero A hd
  have hAi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=((y:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,ite_eq_right hc]
  have hca : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=(c:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [hA0]
    exact cayley_real_boundary x
  have hcb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞)=(d:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [hAi]
    exact cayley_real_boundary y
  have hccl : Complex.orthonormalBasisOneI.repr c ∈ closure (halfPlaneDiscPlane '' ((A • · : ℍ→ℍ) '' S)) :=
    halfPlaneDiscPlane_endpoint_mem_closure (realSL_trace_endpoint_mem_closure A hzero) hca
  have hdcl : Complex.orthonormalBasisOneI.repr d ∈ closure (halfPlaneDiscPlane '' ((A • · : ℍ→ℍ) '' S)) :=
    halfPlaneDiscPlane_endpoint_mem_closure (realSL_trace_endpoint_mem_closure A hinfty) hcb
  have ha0 : Complex.orthonormalBasisOneI.repr (-1) ∈ closure (halfPlaneDiscPlane '' S) :=
    halfPlaneDiscPlane_endpoint_mem_closure hzero cayley_zero_eq_neg_one
  have hai : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ∞=((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty]
  have ha1 : Complex.orthonormalBasisOneI.repr 1 ∈ closure (halfPlaneDiscPlane '' S) :=
    halfPlaneDiscPlane_endpoint_mem_closure hinfty hai
  have hball (T : Set ℍ) : halfPlaneDiscPlane '' T ⊆ ball 0 1 := by
    rintro z ⟨w,_hw,rfl⟩
    rw [←halfPlaneDiscPlane_range]
    exact mem_range_self w
  have hconnA := hSp.image halfPlaneDiscPlane halfPlaneDiscPlane_isOpenEmbedding.continuous.continuousOn
  have hconnB := (hSp.image (A • · : ℍ→ℍ) (isometry_smul ℍ A).continuous.continuousOn).image
    halfPlaneDiscPlane halfPlaneDiscPlane_isOpenEmbedding.continuous.continuousOn
  have hcs : Complex.orthonormalBasisOneI.repr c ∈ sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm,Complex.orthonormalBasisOneI.repr.norm_map]
    exact cayley_real_norm x
  have hds : Complex.orthonormalBasisOneI.repr d ∈ sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm,Complex.orthonormalBasisOneI.repr.norm_map]
    exact cayley_real_norm y
  have hmeet : (closure (halfPlaneDiscPlane '' S) ∩
      closure (halfPlaneDiscPlane '' ((A • · : ℍ→ℍ) '' S))).Nonempty := by
    rcases mul_neg_iff.mp himprod with ⟨hcpos,hdneg⟩ | ⟨hcneg,hdpos⟩
    · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.opposite_semicircle_traces_intersect hconnA hconnB
        (hball S) (hball _) ha0 ha1 hccl hdcl hcs hds
        (by simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hcpos)
        (by simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hdneg)
    · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing.opposite_semicircle_traces_intersect hconnA hconnB
        (hball S) (hball _) ha0 ha1 hdcl hccl hds hcs
        (by simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hdpos)
        (by simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hcneg)
  by_contra hnone
  have hdis : Disjoint S ((A • · : ℍ→ℍ) '' S) := Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp
    hnone)
  have hSB := plane_trace_boundary_subset_of_native hSboundary cayley_zero_eq_neg_one hai
  have hTBnative : closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((A • · : ℍ→ℍ) ''
    S)) ∩ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ⊆
      ({(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rintro z ⟨hz,hzR⟩
    exact realSL_translated_trace_boundary_subset A hSboundary hz hzR
  have hTB := plane_trace_boundary_subset_of_native hTBnative hca hcb
  have hboundary : Disjoint (closure (halfPlaneDiscPlane '' S) ∩ sphere 0 1)
      (closure (halfPlaneDiscPlane '' ((A • · : ℍ→ℍ) '' S)) ∩ sphere 0 1) := by
    apply Set.disjoint_left.mpr
    intro z hzS hzT
    have him0 : (Complex.orthonormalBasisOneI.repr.symm z).im=0 := by
      rcases hSB hzS with rfl | rfl <;> simp
    have himne : (Complex.orthonormalBasisOneI.repr.symm z).im≠0 := by
      rcases hTB hzT with rfl | rfl
      · simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hci
      · simpa only [Complex.orthonormalBasisOneI.repr.symm_apply_apply] using hdi
    exact himne him0
  have hTd : IsClosed ((A • · : ℍ→ℍ) '' S) := (Homeomorph.smul A).isClosedMap S hSc
  have hdiscl := disjoint_plane_trace_closures hSc hTd hdis hboundary
  obtain ⟨z,hz,hz'⟩ := hmeet
  exact Set.disjoint_left.mp hdiscl hz hz'

/-- Native equality-or-disjointness is the original whole H3-axis simplicity predicate. -/
theorem HalfPlaneFuchsianGroup.dilation_isSimple_of_native_axis_stable
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0<l) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (hstable : letI := P.nativeAction
      ∀ h : H, (h • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
        0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier ∨
        Disjoint ((h • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
          0).carrier) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) :
    IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
  let nativeAxisToSimplicityAction := P.nativeAction
  refine ⟨hfH,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl,?_⟩
  intro g hg
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  have ha : (fun z : ℍ => (⟨g,hg⟩ : H) • z)=(A • · : ℍ→ℍ) :=
    funext (P.nativeAction_realSL ⟨g,hg⟩ A hA)
  have hs := hstable ⟨g,hg⟩
  rw [ha] at hs
  have haxis : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [stableAxisDilation_geodesicAxis l hl]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_vertical_image.symm
  have himg : (fun z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g • z) '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' ((A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) := by
    rw [←hA,haxis,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL]
  rw [himg,haxis]
  rcases hs with he | hd
  · exact Or.inl (congrArg (Set.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed) he)
  · exact Or.inr ((Set.disjoint_image_iff
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective).mpr hd)

/-- Every actual cyclic dilation power preserves the entire native axis. -/
theorem HalfPlaneFuchsianGroup.dilation_zpower_axis_image
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (h : H) (hh : h ∈ Subgroup.zpowers (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ :
      H)) :
    letI := P.nativeAction
    (h • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  let nativeDilationPowersAxisAction := P.nativeAction
  have hf : (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) ∈ nativeAxisStabilizer H := by
    change _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l∈H ∧ (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis
    exact ⟨hfH,stableAxisDilation_image_axis l⟩
  have hmem : h ∈ nativeAxisStabilizer H := by
    obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (nativeAxisStabilizer H).zpow_mem hf n
  rw [P.nativeAxisStabilizer_eq] at hmem
  exact hmem

/-- An actual dilation side-pairing has a genuinely simple entire axis, with elliptic elements of the ambient group allowed. -/
theorem HalfPlaneFuchsianGroup.dilation_side_isSimple
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0<l) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {D : Set P.cayleyData.domain.carrier} (hD : IsConvexFuchsianPolygon P.cayleyData D)
    (s : FuchsianPolygonSides P.cayleyData D)
    (hs : (fuchsianSideElement hD s).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹) :
    IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
  let nativeDilationSideSimplicityAction := P.nativeAction
  obtain ⟨w,C,hCc,hCp,hwC,hfwC,hpack⟩ := P.dilation_side_connector l hl hfH hD s hs
  let f : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  let S := cyclicOrbitTrace f C
  have hSc : IsClosed S := P.dilation_connector_trace_isClosed l hl hfH hCc
  have hSp : IsPreconnected S := P.dilation_connector_trace_preconnected l hfH hCp hwC hfwC
  have hzero : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) :=
    P.dilation_trace_zero_mem_closure l hl hfH ⟨w,hwC⟩
  have hinfty : (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S) :=
    P.dilation_trace_infty_mem_closure l hl hfH ⟨w,hwC⟩
  have hbound : closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ''
    S) ∩ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ⊆
      ({((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rintro z ⟨hz,hzR⟩
    exact P.dilation_connector_trace_boundary l hfH hCc z hz hzR
  apply P.dilation_isSimple_of_native_axis_stable l hl hfH
  intro h
  by_cases heq : (h • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  · exact Or.inl heq
  · right
    by_contra hndis
    obtain ⟨z,⟨p,hp,rfl⟩,hzaxis⟩ := Set.not_disjoint_iff.mp hndis
    obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL h.val (P.preserves h)
    have hact : (h • · : ℍ→ℍ)=(A • · : ℍ→ℍ) := funext (P.nativeAction_realSL h A hA)
    rw [hact] at heq hzaxis
    have hprod := axisSL_crossing_product_neg A heq hp hzaxis
    have hmeet := realSL_crossing_traces_intersect hSc hSp hzero hinfty hbound A hprod
    have hnot : h ∉ Subgroup.zpowers f := by
      intro hh
      exact heq (by rw [←hact];exact P.dilation_zpower_axis_image l hfH h hh)
    have hdis := hpack h hnot
    rw [hact] at hdis
    obtain ⟨x,hx,hx'⟩ := hmeet
    exact Set.disjoint_left.mp hdis hx hx'

/-- Reversing the direction of a genuine hyperbolic side does not change its entire axis. -/
theorem HalfPlaneFuchsianGroup.signed_dilation_side_isSimple
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : l≠0) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l∈H)
    (hhyper : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l))
    {D : Set P.cayleyData.domain.carrier} (hD : IsConvexFuchsianPolygon P.cayleyData D)
    (s : FuchsianPolygonSides P.cayleyData D)
    (hs : (fuchsianSideElement hD s).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹) :
    IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · have hfl : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l)∈H := by
      rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg]
      exact H.inv_mem hfH
    have hpaired : (fuchsianSideElement hD (fuchsianPairedSide hD s)).val=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
      rw [fuchsianSideElement_paired]
      change (fuchsianSideElement hD s).val⁻¹=_
      rw [hs,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg]
      group
    have hsp := P.dilation_side_isSimple (-l) (neg_pos.mpr hneg) hfl hD
      (fuchsianPairedSide hD s) hpaired
    refine ⟨hfH,hhyper,?_⟩
    intro g hg
    rw [stableAxisDilation_geodesicAxis_of_ne_zero l hl,
      ←stableAxisDilation_geodesicAxis (-l) (neg_pos.mpr hneg)]
    exact hsp.2.2 g hg
  · exact P.dilation_side_isSimple l hpos hfH hD s hs

/-- Necessity for the actual original convex fundamental polygon; no torsion-free or normalized-model hypothesis is imposed. -/
theorem IsConvexFuchsianPolygon.hyperbolic_side_isSimple
    {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup G}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD s).val) :
    IsSimple G (fuchsianSideElement hD s).val := by
  let hyperbolicSideNecessitySphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
  let hyperbolicSideNecessitySphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩
  let f := (fuchsianSideElement hD s).val
  obtain ⟨q,hq,l,hl,he⟩ := P.hyperbolic_halfPlane_normalizer f hg (fuchsianSideElement hD s).property
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G
  let N := P.normalizedHalfPlaneData q hq
  let Q := N.cayleyData
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q
  have hr : r.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    change (fun z => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val
      z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_
    rw [←image_image,hq,cayleyMobius_image_openHalfPlane]
  let e : G ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K :=
    MulEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      G)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K)
  let F : P.domain.carrier ≃ₜ Q.domain.carrier := P.conjugateCoordinate r hr
  have hEquiv (a : G) (x : P.domain.carrier) : F (a • x)=e a • F x := by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (a.val.val x.val))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (a.val.val (q.val.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val x.val))))))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,q.val.symm_apply_apply]
  have harea : MeasureTheory.Measure.map F P.area=Q.area := P.conjugateCoordinate_area_map r hr
  have hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (F (P.finiteCoordinate.symm z))) :=
    P.conjugateCoordinate_isometry r hr
  obtain ⟨hQ,t,ht⟩ := equivariant_fuchsian_side_element_image P Q e F hEquiv harea hiso hD s
  have htval : (fuchsianSideElement hQ t).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
    have hh := congrArg Subtype.val ht
    change (fuchsianSideElement hQ t).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*(q*f*q⁻¹)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ at hh
    rwa [he] at hh
  have hfK : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l∈K := by
    rw [←he]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q G
      (fuchsianSideElement hD s)).property
  have hhyperK : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
    rw [←he]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f q hg
  have hsp := N.signed_dilation_side_isSimple l hl hfK hhyperK hQ t htval
  rw [←he] at hsp
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G f q).mp hsp

/-- For arbitrary actual original invariant-disc groups and primitive hyperbolics. -/
theorem primitive_hyperbolic_isSidePairing_iff_simple {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup G)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hp : IsPrimitive G f) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    (∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
      ∃ s : FuchsianPolygonSides P D, (fuchsianSideElement hD s).val=f) ↔ IsSimple G f := by
  constructor
  · rintro ⟨D,hD,s,hs⟩
    have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD
      s).val := hs.symm ▸ hf
    exact hs ▸ hD.hyperbolic_side_isSimple s hh
  · exact primitive_simple_hyperbolic_side_pairing P f hp

/-- The actual side-pairing classification includes the genuine simplicity condition on its hyperbolic branch. -/
theorem IsConvexFuchsianPolygon.side_pairing_type_classification
    {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup G}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (fuchsianSideElement hD s).val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (fuchsianSideElement hD s).val ∨ IsSimple G (fuchsianSideElement hD s).val := by
  have hn : (fuchsianSideElement hD s).val≠1 := fun he => (fuchsianSideElement_spec hD s).1 (Subtype.ext he)
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy (fuchsianSideElement hD
    s).val hn with hp | hl | he
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (hD.hyperbolic_side_isSimple s
      ⟨hl,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,P.image_eq (fuchsianSideElement hD s)⟩))
  · exact Or.inl he

end LowDimensionalTopology.Geometry.Fuchsian
