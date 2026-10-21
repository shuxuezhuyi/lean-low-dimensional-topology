module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.HyperbolicSidePairing
public import Mathlib.Topology.LocallyFinite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology OnePoint Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual trace obtained by repeating one compact connector by all integer powers. -/
def cyclicOrbitTrace {G X : Type*} [Group G] [MulAction G X] (g : G) (C : Set X) : Set X :=
  ⋃ n : ℤ, (g^n • ·) '' C

/-- Consecutive translated connectors meet at the translated endpoint. -/
theorem cyclicOrbitTrace_preconnected {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (g : G) (hc : Continuous (g • · : X → X))
    (hc' : Continuous (g⁻¹ • · : X → X)) {C : Set X} (hC : IsPreconnected C)
    {w : X} (hw : w ∈ C) (hgw : g • w ∈ C) : IsPreconnected (cyclicOrbitTrace g C) := by
  have hpow (n : ℤ) : Continuous (g^n • · : X → X) := by
    induction n using Int.induction_on with
    | zero => simp only [zpow_zero, one_smul]; fun_prop
    | succ n hn => simpa only [zpow_add, zpow_one, mul_smul, Function.comp_def] using hn.comp hc
    | pred n hn => simpa only [zpow_sub, zpow_one, mul_smul, Function.comp_def] using hn.comp hc'
  apply IsPreconnected.iUnion_of_chain (fun n => hC.image _ (hpow n).continuousOn)
  intro n
  refine ⟨g^(n+1) • w, ?_, mem_image_of_mem _ hw⟩
  refine ⟨g • w,hgw,?_⟩
  simp only [zpow_add, zpow_one, mul_smul]

/-- Compact-hit finiteness gives local finiteness for the actual dilation copies of any compact connector. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_locallyFinite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hC : IsCompact C) :
    letI := P.nativeAction
    LocallyFinite (fun n : ℤ => (((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)^n) • ·) '' C) := by
  let nativeDilationConnectorAction := P.nativeAction
  obtain ⟨M,hM⟩ := hC.bddAbove_image continuous_halfPlane_logNorm.abs.continuousOn
  intro x
  obtain ⟨B,hB,hxB⟩ := exists_compact_mem_nhds x
  refine ⟨B,hxB,?_⟩
  have hS (z : ℍ) (hz : z ∈ C) : |Real.log ‖(z:ℂ)‖| ≤ M := hM (mem_image_of_mem _ hz)
  have he (n : ℤ) : (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ :
    H)^n = ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ := Subtype.ext rfl
  simpa only [he] using P.dilation_power_hits_finite l hl hfH C M hS B hB

/-- The periodic trace of a compact connector is closed in the genuine native half-plane. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_trace_isClosed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hC : IsCompact C) :
    letI := P.nativeAction
    IsClosed (cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
  let nativeDilationTraceClosedAction := P.nativeAction
  have hlf := P.dilation_connector_locallyFinite l hl hfH hC
  exact hlf.isClosed_iUnion (fun n => (hC.image (P.nativeHom
    ((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)^n)).continuous).isClosed)

/-- A compact native connector stays in a genuine closed cone strictly above the real axis. -/
theorem compact_halfPlane_positive_cone {C : Set ℍ} (hC : IsCompact C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ C, δ * ‖(z:ℂ)‖ ≤ z.im := by
  by_cases hne : C.Nonempty
  · have hc : Continuous (fun z : ℍ => z.im / ‖(z:ℂ)‖) :=
      UpperHalfPlane.continuous_im.div UpperHalfPlane.continuous_coe.norm
        (fun z => norm_ne_zero_iff.mpr z.ne_zero)
    obtain ⟨z,hz,hmin⟩ := hC.exists_isMinOn hne hc.continuousOn
    refine ⟨z.im/‖(z:ℂ)‖,div_pos z.im_pos (norm_pos_iff.mpr z.ne_zero),fun w hw => ?_⟩
    exact (le_div_iff₀ (norm_pos_iff.mpr w.ne_zero)).mp (hmin hw)
  · exact ⟨1,one_pos,fun z hz => (hne ⟨z,hz⟩).elim⟩

/-- Every point of the complete periodic trace satisfies the same positive cone bound. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_trace_cone {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈
      H)
    {C : Set ℍ} (hC : IsCompact C) :
    letI := P.nativeAction
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
      : H) C,
      δ * ‖(z:ℂ)‖ ≤ z.im := by
  let nativeDilationTraceConeAction := P.nativeAction
  obtain ⟨δ,hδ,hCδ⟩ := compact_halfPlane_positive_cone hC
  refine ⟨δ,hδ,?_⟩
  rintro z hz
  obtain ⟨n,w,hw,rfl⟩ := mem_iUnion.mp hz
  have hcoord := P.dilation_element_coe l ((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ :
    H)^n) n rfl w
  change δ * ‖((((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)^n) • w : ℍ):ℂ)‖ ≤ _
  rw [hcoord,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have him : (((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)^n) • w : ℍ).im = Real.exp ((n:ℝ)*l) * w.im := by
    change ((((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)^n) • w : ℍ):ℂ).im = _
    rw [hcoord,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    rfl
  rw [him]
  nlinarith [mul_le_mul_of_nonneg_left (hCδ w hw) (Real.exp_pos ((n:ℝ)*l)).le]


/-- The genuine closed cone, completed by infinity in the actual one-point compactification. -/
def extendedPositiveCone (δ : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  insert ∞ (((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | δ * ‖z‖ ≤ z.im})

theorem extendedPositiveCone_isClosed (δ : ℝ) : IsClosed (extendedPositiveCone δ) := by
  apply (OnePoint.isClosed_iff_of_mem (show ∞ ∈ extendedPositiveCone δ by simp [extendedPositiveCone])).mpr
  have he : ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' extendedPositiveCone δ = {z : ℂ | δ*‖z‖ ≤ z.im} := by
    ext z
    simp [extendedPositiveCone]
  rw [he]
  exact isClosed_le (continuous_const.mul continuous_norm) Complex.continuous_im

/-- A positive cone meets the genuine ideal real boundary only at zero and infinity. -/
theorem extendedPositiveCone_boundary {δ : ℝ} (hδ : 0 < δ) {z :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hz : z ∈ extendedPositiveCone δ) (hb : z ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis) : z = (0:ℂ) ∨ z = ∞ := by
  rcases eq_or_ne z ∞ with rfl | hzi
  · exact Or.inr rfl
  · obtain ⟨w,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hzi
    have hw : δ*‖w‖ ≤ w.im := by simpa [extendedPositiveCone] using hz
    have him := _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_coe w |>.mp hb
    have hn : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact Or.inl (congrArg ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (norm_eq_zero.mp
      hn))

/-- No additional finite ideal endpoint can appear in the actual compactified periodic trace. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_trace_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈
      H)
    {C : Set ℍ} (hC : IsCompact C) :
    letI := P.nativeAction
    ∀ z ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace
      (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C),
      z ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis → z = (0:ℂ) ∨ z = ∞ := by
  let nativeDilationTraceBoundaryAction := P.nativeAction
  obtain ⟨δ,hδ,hcone⟩ := P.dilation_connector_trace_cone l hfH hC
  have hsub : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C ⊆ extendedPositiveCone δ := by
    rintro _ ⟨z,hz,rfl⟩
    exact Or.inr ⟨(z:ℂ),hcone z hz,rfl⟩
  intro z hz hb
  exact extendedPositiveCone_boundary hδ (closure_minimal hsub (extendedPositiveCone_isClosed δ) hz) hb

/-- The periodic trace is truly connected once its connector joins a point to its actual next image. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_trace_preconnected {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈
      H)
    {C : Set ℍ} (hC : IsPreconnected C) {w : ℍ}
    (hw : w ∈ C) (hfw : letI := P.nativeAction; (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) • w ∈ C) :
    letI := P.nativeAction
    IsPreconnected (cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
  let nativeDilationTraceConnectedAction := P.nativeAction
  exact cyclicOrbitTrace_preconnected _ (P.nativeHom _).continuous (P.nativeHom _).continuous hC hw hfw


/-- The actual forward orbit in every nonempty connector approaches infinity. -/
theorem HalfPlaneFuchsianGroup.dilation_trace_infty_mem_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hne : C.Nonempty) :
    letI := P.nativeAction
    ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
  let nativeDilationForwardEndpointAction := P.nativeAction
  obtain ⟨w,hw⟩ := hne
  let a : ℂˣ := Units.mk0 ((Real.exp l : ℝ):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))
  have ha : 1 < ‖(a:ℂ)‖ := by
    simp only [a,Units.val_mk0,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos l)]
    exact Real.one_lt_exp_iff.mpr hl
  have ha1 : (a:ℂ) ≠ 1 := by intro h;rw [h,norm_one] at ha;exact lt_irrefl _ ha
  have he : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement a := _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_scaling_eq_standard a ha1
  have ht := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_expansion_iterates_tendsto a ha (w:ℂ) w.ne_zero
  rw [←he] at ht
  apply mem_closure_of_tendsto ht
  filter_upwards [] with n
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  refine ⟨g^n • w,mem_iUnion_of_mem (n:ℤ) ?_,?_⟩
  · exact ⟨w,hw,by rw [zpow_natCast]⟩
  · exact (P.nativeAction_boundary (g^n) w).symm

/-- The actual backward orbit approaches zero in the genuine one-point compactification. -/
theorem HalfPlaneFuchsianGroup.dilation_trace_zero_mem_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hne : C.Nonempty) :
    letI := P.nativeAction
    ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) C) := by
  let nativeDilationBackwardEndpointAction := P.nativeAction
  obtain ⟨w,hw⟩ := hne
  let a : ℂˣ := Units.mk0 ((Real.exp (-l) : ℝ):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-l)))
  have ha : ‖(a:ℂ)‖ < 1 := by
    simp only [a,Units.val_mk0,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos (-l))]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hl)
  have ha1 : (a:ℂ) ≠ 1 := by intro h;rw [h,norm_one] at ha;exact lt_irrefl _ ha
  have he : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l) = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement a := _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_scaling_eq_standard a ha1
  have ht := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_contraction_iterates_tendsto a ha (w:ℂ)
  rw [←he,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg] at ht
  apply mem_closure_of_tendsto ht
  filter_upwards [] with n
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  refine ⟨g⁻¹^n • w,mem_iUnion_of_mem (-(n:ℤ)) ?_,?_⟩
  · exact ⟨w,hw,by rw [zpow_neg,zpow_natCast,inv_pow]⟩
  · exact (P.nativeAction_boundary (g⁻¹^n) w).symm

/-- The compactified connector trace has precisely the two actual axis endpoints on the ideal boundary. -/
theorem HalfPlaneFuchsianGroup.dilation_connector_trace_ideal_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    {C : Set ℍ} (hC : IsCompact C) (hne : C.Nonempty) :
    letI := P.nativeAction
    closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' cyclicOrbitTrace
      (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H)
      C) ∩ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis =
      {((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} := by
  let nativeDilationTraceIdealBoundaryAction := P.nativeAction
  apply Subset.antisymm
  · exact fun z hz => P.dilation_connector_trace_boundary l hfH hC z hz.1 hz.2
  · rintro z (rfl | rfl)
    · exact ⟨P.dilation_trace_zero_mem_closure l hl hfH hne,by simp⟩
    · exact ⟨P.dilation_trace_infty_mem_closure l hl hfH hne,by simp⟩

end LowDimensionalTopology.Geometry.Fuchsian
