/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalRawWeightedEuler
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.SmallParabolicSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
/-!
# Numerical profiles of raw corner classes

Point stabilizer orders separate ideal, cone and accidental raw classes. Their
weights determine the numerical signature deficit. A parabolic fixed point and
area below pi then force the small-area raw elliptic-order alternatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc

/- BEGIN OWN ORIGINAL RAW PARABOLIC PROFILES -/
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
section ActualRawProfiles
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
  {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
  (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
    hD,v.carrier))
  (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
    originalRefinedEndpointSet hD)
  (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)

/-- The actual stabilizer order of a finite raw-class representative, with zero precisely for an ideal representative. -/
def originalRawCornerClassOrder (q : Quotient (originalRawCornerSetoid J e)) : ℕ :=
  if hq : ‖(originalCyclicVertex hD J hv q.out : ℂ)‖<1 then
    fuchsianPointOrder P (P.finiteCoordinate.symm
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (originalCyclicVertex hD J hv q.out) hq))
  else 0

theorem originalRawCornerClassWeight_out (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawCornerClassWeight hD ha J hc hv e hs q=originalRawCornerWeight hD J hv q.out := by
  calc
    _=originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ q.out):=
      congrArg (originalRawCornerClassWeight hD ha J hc hv e hs) (Quotient.out_eq q).symm
    _=_:=rfl

theorem originalRawCornerClassWeight_order (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawCornerClassWeight hD ha J hc hv e hs q=1/(originalRawCornerClassOrder hD J hv e q : ℝ) := by
  rw [originalRawCornerClassWeight_out,originalRawCornerWeight,originalRawCornerClassOrder]
  split_ifs <;> simp

include ha hc hs in
/-- The class order agrees with the actual point order at every finite representative. -/
theorem originalRawCornerClassOrder_finite (i : ZMod J.n) (x : P.domain.carrier)
    (hi : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    originalRawCornerClassOrder hD J hv e (Quotient.mk _ i)=fuchsianPointOrder P x := by
  have h:=originalRawCornerClassWeight_finite hD ha J hc hv e hs i x hi
  rw [originalRawCornerClassWeight_order] at h
  have hn : (originalRawCornerClassOrder hD J hv e (Quotient.mk _ i) : ℝ)=
      (fuchsianPointOrder P x : ℝ):=inv_injective (by simpa only [one_div] using h)
  exact_mod_cast hn

theorem originalRawCornerClassOrder_pos_iff (q : Quotient (originalRawCornerSetoid J e)) :
    0<originalRawCornerClassOrder hD J hv e q ↔ ‖(originalCyclicVertex hD J hv q.out : ℂ)‖<1 := by
  unfold originalRawCornerClassOrder
  split_ifs with hq
  · exact ⟨fun _=>hq,fun _=>P.pointOrder_pos _⟩
  · simp only [lt_self_iff_false,false_iff]
    exact hq

theorem originalRawCornerClassWeight_bounds (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawCornerClassWeight hD ha J hc hv e hs q∈Icc (0 : ℝ) 1 := by
  rw [originalRawCornerClassWeight_order]
  constructor
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · by_cases hn : originalRawCornerClassOrder hD J hv e q=0
    · simp only [hn,Nat.cast_zero,div_zero,zero_le_one]
    · have hn' : (1 : ℝ)≤originalRawCornerClassOrder hD J hv e q:=by exact_mod_cast (show 1≤originalRawCornerClassOrder hD J hv e q by omega)
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hn'

theorem originalRawCornerClassWeight_zero_iff_order (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawCornerClassWeight hD ha J hc hv e hs q=0 ↔ originalRawCornerClassOrder hD J hv e q=0 := by
  rw [originalRawCornerClassWeight_order]
  simp

theorem originalRawCornerClassWeight_zero_iff_ideal (q : Quotient (originalRawCornerSetoid J e)) :
    originalRawCornerClassWeight hD ha J hc hv e hs q=0 ↔
      ‖(originalCyclicVertex hD J hv q.out : ℂ)‖=1 := by
  have hz : originalRawCornerClassOrder hD J hv e q=0 ↔ ¬0<originalRawCornerClassOrder hD J hv e q:=by omega
  rw [originalRawCornerClassWeight_zero_iff_order,hz,originalRawCornerClassOrder_pos_iff]
  exact ⟨fun h=>le_antisymm (originalCyclicVertex hD J hv q.out).norm_le_one (le_of_not_gt h),
    fun h=>by rw [h];exact lt_irrefl 1⟩

/-- Only actual zero-weight raw classes are counted as ideal classes. -/
def originalRawZeroClassCount : ℕ :=
  (Finset.univ.filter (fun q : Quotient (originalRawCornerSetoid J e)=>
    originalRawCornerClassWeight hD ha J hc hv e hs q=0)).card

/-- Actual finite raw classes with nontrivial finite stabilizer; accidental classes are omitted. -/
def originalRawConeClasses : Finset (Quotient (originalRawCornerSetoid J e)) :=
  Finset.univ.filter (fun q=>0<originalRawCornerClassWeight hD ha J hc hv e hs q ∧
    originalRawCornerClassWeight hD ha J hc hv e hs q<1)

theorem originalRawConeClasses_order_two_le (q : Quotient (originalRawCornerSetoid J e))
    (hq : q∈originalRawConeClasses hD ha J hc hv e hs) :
    2≤originalRawCornerClassOrder hD J hv e q := by
  have h:= (Finset.mem_filter.mp hq).2
  rw [originalRawCornerClassWeight_order] at h
  have hn : originalRawCornerClassOrder hD J hv e q≠0:=by intro he;simpa [he] using h.1
  have hn' : originalRawCornerClassOrder hD J hv e q≠1:=by intro he;simpa [he] using h.2
  omega

/-- The entries are the genuine actual point stabilizer orders of precisely the nonaccidental finite raw classes. -/
def originalRawEllipticOrders : List ℕ :=
  (originalRawConeClasses hD ha J hc hv e hs).toList.map (originalRawCornerClassOrder hD J hv e)

theorem originalRawEllipticOrders_two_le (m : ℕ) (hm : m∈originalRawEllipticOrders hD ha J hc hv e hs) : 2≤m := by
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hm
  exact originalRawConeClasses_order_two_le hD ha J hc hv e hs q (Finset.mem_toList.mp hq)


/-- The finite-cone contribution is exactly the list of actual nontrivial point stabilizer orders. -/
theorem originalRawEllipticOrders_sum :
    ((originalRawEllipticOrders hD ha J hc hv e hs).map (fun m : ℕ=>1-1/(m:ℝ))).sum=
      ∑q∈originalRawConeClasses hD ha J hc hv e hs,(1-originalRawCornerClassWeight hD ha J hc hv e hs q) := by
  rw [originalRawEllipticOrders,List.map_map,Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro q _
  rw [originalRawCornerClassWeight_order]
  rfl

/-- Actual ideal, nontrivial elliptic and accidental raw classes partition the full weighted Euler sum. -/
theorem originalRawCornerClasses_deficit_partition :
    ∑q : Quotient (originalRawCornerSetoid J e),(1-originalRawCornerClassWeight hD ha J hc hv e hs q)=
      (originalRawZeroClassCount hD ha J hc hv e hs : ℝ)+
        ((originalRawEllipticOrders hD ha J hc hv e hs).map (fun m : ℕ=>1-1/(m:ℝ))).sum := by
  let w:=originalRawCornerClassWeight hD ha J hc hv e hs
  have hsplit (q : Quotient (originalRawCornerSetoid J e)) :
      1-w q=(if w q=0 then 1 else 0)+(if 0<w q ∧ w q<1 then 1-w q else 0) := by
    have hb:=originalRawCornerClassWeight_bounds hD ha J hc hv e hs q
    by_cases hz : w q=0
    · simp [hz]
    · have hp : 0<w q:=lt_of_le_of_ne hb.1 (Ne.symm hz)
      by_cases hl : w q<1
      · simp [hz,hp,hl]
      · have he : w q=1:=le_antisymm hb.2 (le_of_not_gt hl)
        simp [he]
  have hzero : (∑q : Quotient (originalRawCornerSetoid J e),if w q=0 then (1:ℝ) else 0)=
      (originalRawZeroClassCount hD ha J hc hv e hs : ℝ) := by
    rw [←Finset.sum_filter]
    simp only [originalRawZeroClassCount,Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  have hcone : (∑q : Quotient (originalRawCornerSetoid J e),
      if 0<w q ∧ w q<1 then 1-w q else 0)=
      ((originalRawEllipticOrders hD ha J hc hv e hs).map (fun m : ℕ=>1-1/(m:ℝ))).sum := by
    rw [←Finset.sum_filter,originalRawEllipticOrders_sum]
    rfl
  calc
    _=∑q : Quotient (originalRawCornerSetoid J e),
        ((if w q=0 then 1 else 0)+(if 0<w q ∧ w q<1 then 1-w q else 0)):=
      Finset.sum_congr rfl (fun q _=>hsplit q)
    _=_:=by rw [Finset.sum_add_distrib,hzero,hcone]

/-- Numerical data extracted from actual raw classes. The genus argument will be supplied by the actual word realization. -/
def originalRawNumericalSignature (g : ℕ) : FuchsianSignature where
  genus:=g
  ellipticOrders:=originalRawEllipticOrders hD ha J hc hv e hs
  ellipticOrders_two_le:=originalRawEllipticOrders_two_le hD ha J hc hv e hs
  parabolicEnds:=originalRawZeroClassCount hD ha J hc hv e hs
  boundaryHyperbolicEnds:=0

theorem originalRawNumericalSignature_deficit (g : ℕ) :
    (originalRawNumericalSignature hD ha J hc hv e hs g).deficit=
      2*(g:ℝ)-2+∑q : Quotient (originalRawCornerSetoid J e),
        (1-originalRawCornerClassWeight hD ha J hc hv e hs q) := by
  rw [originalRawCornerClasses_deficit_partition]
  simp only [originalRawNumericalSignature,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit,Nat.cast_zero,add_zero]
  ring


/-- Every actual ideal boundary point is an original marked ideal corner, hence contributes an actual zero-weight class. -/
theorem originalRawZeroClassCount_pos_of_idealBoundary (η : ℂ)
    (hη : η∈fuchsianPolygonIdealBoundary P D) : 0<originalRawZeroClassCount hD ha J hc hv e hs := by
  let Q:=originalCyclicDiscPolygon hD ha J hv e hs
  obtain ⟨hcl,hn⟩:=(mem_fuchsianPolygonIdealBoundary P D η).mp hη
  have hI : Q.complexInterior=(fun x=>(P.finiteCoordinate x : ℂ)) '' D := by
    rw [←Q.interior_complex_image,originalCyclicDiscPolygon_interior,image_image]
  rw [←hI,Q.closure_complexInterior] at hcl
  have hnot : η∉Q.complexInterior:=by
    intro h
    have hnorm : ‖η‖<1:=by simpa only [Metric.mem_ball,dist_zero_right] using Q.complexInterior_subset_disc h
    rw [hn] at hnorm
    exact (lt_irrefl 1) hnorm
  obtain ⟨z,hz,hzη⟩:=hcl.resolve_left hnot
  have hzN : ‖(z:ℂ)‖=1:=hzη ▸ hn
  obtain ⟨i,hi⟩:=mem_iUnion.mp hz
  have hpq : Q.vertices i≠Q.vertices (finRotate J.n i):=Q.vertices_injective.ne (Q.next_ne_self i).symm
  rcases original_segment_ideal_eq_endpoint _ _ z hpq hi hzN with he|he
  · have hzero : originalRawCornerClassWeight hD ha J hc hv e hs
        (Quotient.mk _ (originalCyclicFinIndex J i))=0:=by
      apply originalRawCornerClassWeight_ideal
      change ‖(Q.vertices i : ℂ)‖=1
      rwa [←he]
    exact Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩⟩
  · have hzero : originalRawCornerClassWeight hD ha J hc hv e hs
        (Quotient.mk _ (originalCyclicFinIndex J (finRotate J.n i)))=0:=by
      apply originalRawCornerClassWeight_ideal
      change ‖(Q.vertices (finRotate J.n i) : ℂ)‖=1
      rwa [←he]
    exact Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩⟩

/-- A genuine parabolic in the original group forces a genuine ideal raw class; no cusp count is assumed. -/
theorem originalRawZeroClassCount_pos_of_parabolic (f : H) (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) :
    0<originalRawZeroClassCount hD ha J hc hv e hs := by
  obtain ⟨ξ,hξ⟩:=_root_.LowDimensionalTopology.Geometry.Mobius.Classification.exists_fixedPoint (_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear f.val)
  have hfix : f.val.val ξ=ξ:=by simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear_apply] using hξ
  obtain ⟨_g,η,_hg,hη⟩:=hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary f hf ξ hfix
  exact originalRawZeroClassCount_pos_of_idealBoundary hD ha J hc hv e hs η hη

end ActualRawProfiles
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

/-- Actual finite-area original data with a parabolic and area below pi yield the numerical
raw-class alternatives, with genus supplied by the genuine boundary-word realization. -/
theorem finite_area_parabolic_original_raw_profiles {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (f : H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hsmall : (P.area D).toReal<Real.pi) :
    ∃J : PolygonalCircle,∃e : ZMod J.n≃OriginalRefinedSide hD,
    ∃hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier),
    ∃hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD,
    ∃hs : ∀i,J.edgeSegment i=(e i).planeCarrier,
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus
      ((originalCyclicPresentation J e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧ g=0 ∧
      originalRawZeroClassCount hD ha J hc hv e hs=1 ∧
      ((∃q : ℕ,3≤q ∧ (originalRawEllipticOrders hD ha J hc hv e hs).Perm [2,q]) ∨
        (∃q : ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ (originalRawEllipticOrders hD ha J hc hv e hs).Perm [3,q])) := by
  obtain ⟨J,e,hc,hv,hs,g,hg,hArea⟩:=finite_area_original_raw_weightedEuler hD ha
  let S:=originalRawNumericalSignature hD ha J hc hv e hs g
  have hEq : S.areaFormulaValue=(P.area D).toReal:=by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue,originalRawNumericalSignature_deficit]
    exact hArea.symm
  have hpos : 0<(P.area D).toReal:=by
    have hQ:=(originalCyclicDiscPolygon hD ha J hv e hs).area_pos
    rw [originalCyclicDiscPolygon_area hD ha J hv e hs] at hQ
    exact ENNReal.toReal_pos (ne_of_gt hQ) ha
  have hends : 1≤S.parabolicEnds:=by
    exact originalRawZeroClassCount_pos_of_parabolic hD ha J hc hv e hs f hf
  obtain ⟨hgenus,hcusp,_hBoundary,horders⟩:=parabolic_signature_area_below_pi S hends
    (by rw [hEq];exact hpos) (by rw [hEq];exact hsmall)
  exact ⟨J,e,hc,hv,hs,g,hg,hgenus,hcusp,horders⟩

end LowDimensionalTopology.Geometry.Fuchsian
