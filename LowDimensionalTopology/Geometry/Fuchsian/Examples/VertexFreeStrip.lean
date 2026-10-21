/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RawVertexChartRecovery
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology Filter
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian.VertexFreeStrip
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

def shiftDilation : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num))

theorem shiftDilation_re (z:ℍ) : (shiftDilation z).re=2*z.re+1 := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num)) •z).re=_
  rw [mul_smul]
  change (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 •(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num) •z):ℍ):ℂ)).re=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp only [Complex.add_re,Complex.ofReal_re]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num) •z).re+1=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re]

theorem shiftDilation_inv_re (z:ℍ) : ((shiftDilation⁻¹) z).re=(z.re-1)/2 := by
  have h:=shiftDilation_re (shiftDilation.symm z)
  rw [shiftDilation.apply_symm_apply] at h
  change (shiftDilation.symm z).re=_
  linarith

def sideSet (i:Fin 2) : Set ℍ := {z|z.re=(i.val:ℝ)}

theorem sideSet_nonempty (i:Fin 2) : (sideSet i).Nonempty :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe i.val 1 (by norm_num),rfl⟩

theorem sideSet_injective : Function.Injective sideSet := by
  intro i j hij
  have h:((i.val:ℝ))=(j.val:ℝ):=by
    have hx:_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe i.val 1 (by norm_num)∈sideSet j:=
      hij ▸(show _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe i.val 1 (by norm_num)∈sideSet i from rfl)
    exact hx
  exact Fin.ext (by exact_mod_cast h)

def polygon : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ where
  interior:={z|0<z.re∧z.re<1}
  interior_nonempty:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (1/2) 1 (by norm_num),by norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]⟩
  sides:=range sideSet
  sides_nonempty:=⟨sideSet 0,mem_range_self _⟩
  side_nonempty:=by rintro _ ⟨i,rfl⟩;exact sideSet_nonempty i
  disjoint:=by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨s,⟨i,rfl⟩,hi⟩
    change z.re=(i.val:ℝ) at hi
    fin_cases i <;> norm_num at hi <;> simp_all

def sideIndex : Fin 2≃polygon.Side := Equiv.ofBijective
  (fun i=>⟨sideSet i,mem_range_self _⟩)
  ⟨fun _ _ h=>sideSet_injective (congrArg Subtype.val h),by rintro ⟨s,i,rfl⟩;exact ⟨i,rfl⟩⟩

@[simp] theorem sideIndex_val (i:Fin 2) : (sideIndex i).val=sideSet i := rfl

theorem polygon_boundary : polygon.boundary={z:ℍ|z.re=0∨z.re=1} := by
  ext z
  simp only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon.boundary,polygon,mem_sUnion,mem_range,exists_exists_eq_and,
    mem_ofPred_eq,sideSet]
  constructor
  · rintro ⟨i,hi⟩;fin_cases i <;> simp_all
  · rintro (h|h)
    · exact ⟨0,by simpa using h⟩
    · exact ⟨1,by simpa using h⟩

theorem polygon_carrier : polygon.carrier={z:ℍ|0≤z.re∧z.re≤1} := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon.carrier,polygon_boundary]
  ext z
  change (0<z.re∧z.re<1)∨z.re=0∨z.re=1 ↔0≤z.re∧z.re≤1
  constructor
  · rintro (h|h|h) <;> constructor <;> linarith
  · intro h
    by_cases h0:z.re=0
    · exact Or.inr (Or.inl h0)
    by_cases h1:z.re=1
    · exact Or.inr (Or.inr h1)
    exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm h0),lt_of_le_of_ne h.2 h1⟩

def pairing : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) polygon where
  paired:=sideIndex.symm.trans ((Equiv.swap 0 1).trans sideIndex)
  involutive:=by
    intro s
    simp
  element:=fun s=>if sideIndex.symm s=0 then shiftDilation else shiftDilation⁻¹
  element_paired:=by
    intro s
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    fin_cases i <;> simp
  side_image:=by
    intro s
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    fin_cases i
    · simp [sideIndex_val,sideSet]
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        change (shiftDilation w).re=1
        rw [shiftDilation_re];change w.re=0 at hw;linarith
      · intro hz
        refine ⟨shiftDilation.symm z,?_,shiftDilation.apply_symm_apply z⟩
        change (shiftDilation.symm z).re=0
        rw [show shiftDilation.symm=shiftDilation⁻¹ from rfl,shiftDilation_inv_re]
        change z.re=1 at hz;linarith
    · simp [sideIndex_val,sideSet]
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        change ((shiftDilation⁻¹) w).re=0
        rw [shiftDilation_inv_re];change w.re=1 at hw;linarith
      · intro hz
        refine ⟨shiftDilation z,?_,shiftDilation.symm_apply_apply z⟩
        change (shiftDilation z).re=1
        rw [shiftDilation_re];change z.re=0 at hz;linarith

theorem interior_open : IsOpen polygon.interior :=
  isOpen_Ioo.preimage UpperHalfPlane.continuous_re

theorem carrier_closure : polygon.carrier=closure polygon.interior := by
  rw [polygon_carrier]
  change UpperHalfPlane.re ⁻¹' Icc 0 1=closure (UpperHalfPlane.re ⁻¹' Ioo 0 1)
  rw [←UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,
    closure_Ioo (by norm_num : (0:ℝ)≠1)]

theorem regular_open : interior (closure polygon.interior)=polygon.interior := by
  rw [←carrier_closure,polygon_carrier]
  change interior (UpperHalfPlane.re ⁻¹' Icc 0 1)=UpperHalfPlane.re ⁻¹' Ioo 0 1
  rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
    interior_Icc]

theorem interior_connected : IsConnected polygon.interior := by
  refine ⟨polygon.interior_nonempty,?_⟩
  apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
  have he:((↑):ℍ→ℂ) ''polygon.interior=
      {z:ℂ|0<z.im}∩({z:ℂ|0<z.re}∩{z:ℂ|z.re<1}):=by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩;exact ⟨w.im_pos,hw⟩
    · rintro ⟨hi,hr⟩;exact ⟨⟨z,hi⟩,hr,rfl⟩
  rw [he]
  exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter
    ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).inter
      (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear 1))).isPreconnected

theorem frontier_boundary : frontier polygon.interior=polygon.boundary := by
  rw [frontier,interior_open.interior_eq,←carrier_closure,polygon_carrier,polygon_boundary]
  ext z
  change (0≤z.re∧z.re≤1)∧¬(0<z.re∧z.re<1) ↔z.re=0∨z.re=1
  constructor
  · intro h;by_cases h0:z.re=0
    · exact Or.inl h0
    · right;by_contra h1;apply h.2
      exact ⟨lt_of_le_of_ne h.1.1 (Ne.symm h0),lt_of_le_of_ne h.1.2 h1⟩
  · rintro (h|h) <;> simp [h]

def geometry : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry polygon ∅ where
  interior_open:=interior_open
  interior_connected:=interior_connected
  carrier_closure:=carrier_closure
  regular_open:=regular_open
  frontier_boundary:=frontier_boundary
  locallyFinite:=by
    let : Finite polygon.Side:=Finite.of_surjective sideIndex sideIndex.surjective
    exact locallyFinite_of_finite _
  side_closed:=by
    intro s;obtain ⟨i,rfl⟩:=sideIndex.surjective s
    exact isClosed_eq UpperHalfPlane.continuous_re continuous_const
  vertex_discrete:=Set.finite_empty.isDiscrete
  line:=fun s=>.vertical (sideIndex.symm s).val
  side_subset_line:=by
    intro s;obtain ⟨i,rfl⟩:=sideIndex.surjective s
    simp only [Equiv.symm_apply_apply]
    exact Subset.rfl
  side_two_points:=by
    intro s;obtain ⟨i,rfl⟩:=sideIndex.surjective s
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe i.val 1 (by norm_num),rfl,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe i.val 2 (by norm_num),rfl,?_⟩
    intro h;have h':(1:ℝ)=2:=congrArg UpperHalfPlane.im h;norm_num at h'
  side_meet_vertex:=by
    intro s t hst x hxs hxt
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    obtain ⟨j,rfl⟩:=sideIndex.surjective t
    apply False.elim (hst ?_)
    apply congrArg sideIndex
    apply Fin.ext
    have h:(i.val:ℝ)=(j.val:ℝ):=hxs.symm.trans hxt
    exact_mod_cast h
  side_interval:=by
    intro s _x _hx _hv
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    exact Filter.Eventually.of_forall (fun _=>by simp only [Equiv.symm_apply_apply];rfl)

local instance stripIndexTopology : TopologicalSpace pairing.Generated:=⊥
local instance stripIndexDiscrete : DiscreteTopology pairing.Generated:=⟨rfl⟩
local instance stripIsometricAction : IsIsometricSMul pairing.Generated ℍ:=⟨fun g=>g.val.isometry⟩

theorem element_sideIndex (i:Fin 2) : pairing.element (sideIndex i)=
    if i=0 then shiftDilation else shiftDilation⁻¹ := by
  simp [pairing]

theorem opposite_sides (s:polygon.Side) (x:ℍ) (hx:x∈s.val) :
    pairing.OppositeSideNeighborhoods s x := by
  apply (pairing.oppositeSideNeighborhoods_iff s x).mpr
  obtain ⟨i,rfl⟩:=sideIndex.surjective s
  rw [polygon_carrier]
  change {z:ℍ|0≤z.re∧z.re≤1}∪
    (fun z:ℍ=>pairing.element (sideIndex i) z)⁻¹'{z:ℍ|0≤z.re∧z.re≤1}∈𝓝 x
  rw [element_sideIndex]
  fin_cases i
  · have hx0:x.re=0:=by simpa [sideSet] using hx
    simp only [show (⟨0,by decide⟩:Fin 2)=0 from rfl,ite_true]
    apply Filter.mem_of_superset ((isOpen_Ioo.preimage UpperHalfPlane.continuous_re).mem_nhds
      (show x∈UpperHalfPlane.re⁻¹'Ioo (-1/2:ℝ) 1 by change -1/2<x.re∧x.re<1;rw [hx0];norm_num))
    intro z hz
    change (0≤z.re∧z.re≤1)∨(0≤(shiftDilation z).re∧(shiftDilation z).re≤1)
    rw [shiftDilation_re]
    by_cases h:0≤z.re
    · exact Or.inl ⟨h,hz.2.le⟩
    · right;constructor <;> linarith [hz.1]
  · have hx1:x.re=1:=by simpa [sideSet] using hx
    simp only [show (⟨1,by decide⟩:Fin 2)≠0 by decide,ite_false]
    apply Filter.mem_of_superset ((isOpen_Ioo.preimage UpperHalfPlane.continuous_re).mem_nhds
      (show x∈UpperHalfPlane.re⁻¹'Ioo (0:ℝ) 3 by change 0<x.re∧x.re<3;rw [hx1];norm_num))
    intro z hz
    change (0≤z.re∧z.re≤1)∨(0≤((shiftDilation⁻¹) z).re∧((shiftDilation⁻¹) z).re≤1)
    rw [shiftDilation_inv_re]
    by_cases h:z.re≤1
    · exact Or.inl ⟨hz.1.le,h⟩
    · right;constructor <;> linarith [hz.2]

theorem finiteFiberLocalTessellationCondition : pairing.FiniteFiberLocalTessellationCondition :=
  geometry.local_tessellation pairing (fun _ hx=>False.elim hx) (fun s x hx _=>opposite_sides s x hx)

theorem generated_preserves_right (g:pairing.Generated) (z:ℍ) :
    0<z.re+1 ↔0<(g.val z).re+1 := by
  have hall:∀(f:ℍ≃ᵢℍ),f∈pairing.Generated→∀z:ℍ,0<z.re+1↔0<(f z).re+1:=by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf=>
      obtain ⟨s,rfl⟩:=hf
      obtain ⟨i,rfl⟩:=sideIndex.surjective s
      rw [element_sideIndex]
      split_ifs
      · intro w;rw [shiftDilation_re];constructor <;> intro h <;> linarith
      · intro w;rw [shiftDilation_inv_re];constructor <;> intro h <;> linarith
    | one=>intro w;exact Iff.rfl
    | mul a b _ _ iha ihb=>intro w;exact (ihb w).trans (iha (b w))
    | inv a _ iha=>
      intro w
      have h:=iha (a.symm w)
      rw [a.apply_symm_apply] at h
      exact h.symm
  exact hall g.val g.property z

theorem evaluation_not_surjective : ¬Function.Surjective pairing.evaluation := by
  intro hs
  obtain ⟨q,hq⟩:=hs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 (by norm_num))
  obtain ⟨a,rfl⟩:=Quotient.exists_rep q
  have ha:0≤a.2.val.re:=((congrArg (fun T:Set ℍ=>a.2.val∈T) polygon_carrier).mp a.2.property).1
  have hr:0<(a.1.val a.2.val).re+1:=
    (generated_preserves_right a.1 a.2.val).mp (by linarith)
  have hh:=congrArg UpperHalfPlane.re hq
  change (a.1.val a.2.val).re=(-2:ℝ) at hh
  linarith

theorem no_uniform_charts (ε:ℝ) (hε:0<ε) : ¬Nonempty (_root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts pairing.evaluation ε) := by
  rintro ⟨hc⟩
  exact evaluation_not_surjective
    (finiteFiberLocalTessellationCondition.evaluation_homeomorph_of_uniform_charts pairing interior_connected
      carrier_closure.le hε hc).surjective

theorem no_uniform_raw_radius (r:ℝ) : ¬pairing.UniformLocalTessellationRadius r := by
  intro hr
  have hc:IsConnected polygon.carrier:=by rw [carrier_closure];exact interior_connected.closure
  exact evaluation_not_surjective (finiteFiberLocalTessellationCondition.covering_homeomorph_evaluation pairing hr
    hc).2.surjective

theorem not_fundamentalDomain :
    ¬_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain pairing.Generated ℍ MeasureTheory.volume polygon.interior := by
  intro hd
  let q:ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 (by norm_num)
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_meetsEveryOrbit pairing.Generated ℍ hd q
  rw [←carrier_closure,polygon_carrier] at hg
  have hq:0<q.re+1:=(generated_preserves_right g q).mpr (by change 0<(g•q).re+1;linarith [hg.1])
  norm_num [q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hq

/--
The no-finite-vertex remark has an actual hyperbolic-plane model even for
the corrected developing-chart meaning of the uniform radius. Both sides are entire
native vertical geodesics and the genuine pairing is z ↦ 2z+1.
-/
theorem vertex_free_polygon_without_uniform_radius :
    ∃(P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon
      ℍ)(S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P),
      Nonempty (_root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P ∅)∧
      (∀s:P.Side,∀x∈s.val,S.OppositeSideNeighborhoods s x)∧
      S.FiniteVertexCycleCondition ∅∧S.FiniteFiberLocalTessellationCondition∧
      (¬_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ
        MeasureTheory.volume P.interior)∧
      (∀r:ℝ,¬S.UniformLocalTessellationRadius r)∧
      (∀ε:ℝ,0<ε→¬Nonempty (_root_.LowDimensionalTopology.Geometry.Hyperbolic.UniformHyperbolicBallCharts S.evaluation
        ε)) :=
  ⟨polygon,pairing,⟨geometry⟩,opposite_sides,pairing.finiteVertexCycleCondition_empty,
    finiteFiberLocalTessellationCondition,not_fundamentalDomain,no_uniform_raw_radius,no_uniform_charts⟩

end LowDimensionalTopology.Geometry.Fuchsian.VertexFreeStrip
