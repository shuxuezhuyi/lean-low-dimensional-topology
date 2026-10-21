/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FuchsianQuotientAreaBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.CuspAreaNeighborhoods
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompletionConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalCompletionWeightedEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance compactAreaLocalSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance compactAreaLocalSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem fuchsianQuotientAreaMeasure_locally_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H
      P.domain.carrier) :
    ∃U : Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H P.domain.carrier),IsOpen U∧x∈U∧fuchsianQuotientAreaMeasure P U≠⊤ := by
  let _compactAreaLocalSMul : ContinuousConstSMul H P.domain.carrier:=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  induction x using Quotient.inductionOn with
  | h x=>
    let R:ℝ:=(‖(P.finiteCoordinate x:ℂ)‖+1)/2
    have hRx : ‖(P.finiteCoordinate x:ℂ)‖<R:=by dsimp only [R];linarith [(P.finiteCoordinate x).norm_lt_one]
    have hR : R<1:=by dsimp only [R];linarith [(P.finiteCoordinate x).norm_lt_one]
    let V:Set P.domain.carrier:={y | ‖(P.finiteCoordinate y:ℂ)‖<R}
    have hV : IsOpen V:=isOpen_lt
      ((continuous_subtype_val.comp P.finiteCoordinate.continuous).norm) continuous_const
    have hVA : P.area V≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure (Metric.closedBall (0:ℂ) R) := by
      rw [P.area_apply V hV.measurableSet,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea]
      apply measure_mono
      rintro z ⟨w,⟨y,hy,rfl⟩,rfl⟩
      exact (Metric.mem_closedBall.trans (by rw [dist_zero_right])).mpr hy.le
    have hfinite : P.area V≠⊤:=ne_top_of_le_ne_top
      (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure_closedBall_integral R hR];exact ENNReal.ofReal_ne_top) hVA
    refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier '' V,
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_isOpenMap H
        P.domain.carrier) V hV,⟨x,hRx,rfl⟩,?_⟩
    exact ne_top_of_le_ne_top hfinite (fuchsianQuotientAreaMeasure_image_le P V hV.measurableSet)


theorem compact_cuspCompletion_quotient_area_ne_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) [CompactSpace (FuchsianCuspCompletion P.asFuchsianDisc)] :
    fuchsianQuotientAreaMeasure P univ≠⊤ := by
  classical
  let D:=P.asFuchsianDisc
  let C:=fuchsianCuspChartNormalization D
  let old:=fuchsianCuspCompletionOld D
  have hold:=fuchsianCuspCompletionOld_isOpenEmbedding D
  have hlocal : ∀x:FuchsianCuspCompletion D,
      ∃U:Set (FuchsianCuspCompletion D),IsOpen U∧x∈U∧
        fuchsianQuotientAreaMeasure P (old ⁻¹' U)≠⊤ := by
    intro x
    rcases fuchsianCuspCompletion_old_or_cusp D x with ⟨y,rfl⟩|⟨c,rfl⟩
    · obtain ⟨V,hV,hy,hfinite⟩:=fuchsianQuotientAreaMeasure_locally_finite P y
      refine ⟨old '' V,hold.isOpenMap V hV,⟨y,hy,rfl⟩,?_⟩
      rwa [preimage_image_eq _ hold.injective]
    · obtain ⟨V,hV,hfinite,hcover⟩:=unitDisc_cusp_completion_deep_finite_area P c
      refine ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspDeepNeighborhood C c,
        _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspDeepNeighborhood_isOpen C D.discontinuous
          (fuchsianParabolicPointRepresentative_orbits_distinct D) (fuchsianCuspChart_full_stabilizer D) c,
        _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewPoint_mem_deep C c,?_⟩
      exact ne_top_of_le_ne_top hfinite ((measure_mono hcover).trans
        (fuchsianQuotientAreaMeasure_image_le P V hV.measurableSet))
  choose U hU hmem hfinite using hlocal
  have hcover : (univ:Set (FuchsianCuspCompletion D))⊆⋃x,U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,hmem x⟩
  obtain ⟨s,hs⟩:=isCompact_univ.elim_finite_subcover U hU hcover
  have hpre : (univ:Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H P.domain.carrier))⊆⋃i∈s,old ⁻¹' U i := by
    intro x _
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hs (mem_univ (old x)))
    obtain ⟨his,hxi⟩:=mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨his,hxi⟩⟩
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun i _=>hfinite i))
    ((measure_mono hpre).trans (measure_biUnion_finset_le s (fun i=>old ⁻¹' U i)))


theorem compact_cuspCompletion_unitDisc_fundamental_area_ne_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) [CompactSpace (FuchsianCuspCompletion P.asFuchsianDisc)]
    {F : Set P.domain.carrier} (hF : IsFuchsianFundamentalDomain P F) : P.area F≠⊤ := by
  rw [fuchsianFundamentalDomain_quotient_area P F hF]
  exact compact_cuspCompletion_quotient_area_ne_top P

theorem compact_cuspCompletion_geometricArea_ne_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [CompactSpace (FuchsianCuspCompletion D)]
    [Finite (FuchsianCyclicConjugacyClasses D .parabolic)]
    (F : Set (fuchsianGeometricDomain D).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) F) :
    geometricModelArea D F≠⊤ := by
  let _compactAreaNormalizedCompletion : CompactSpace (FuchsianCuspCompletion (geometricDiscData D).asFuchsianDisc):=by
    rw [geometricDiscData_asFuchsianDisc]
    exact (fuchsianCuspCompletionConjugacyHomeomorph D (geometricDiscNormalizer D)).compactSpace
  have hL:=finite_area_geometricDisc_fundamental_image D F hF
  have ha:=compact_cuspCompletion_unitDisc_fundamental_area_ne_top (geometricDiscData D) hL
  rwa [geometricDisc_fundamental_area_eq_original D F hF hL] at ha

end LowDimensionalTopology.Geometry.Fuchsian
