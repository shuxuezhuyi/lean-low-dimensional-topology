/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every genuine original Fuchsian cusp chart sends the entire original invariant disc to an actual upper horizontal half-plane. The stable cusp disc forces the upper branch, including when the original group has elliptics. -/
theorem cuspNormalization_original_domain_upper {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain} {p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p) :
    ∃h : ℝ,C.normalizer.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h∧h≤C.height := by
  let E:=C.normalizer.val '' D.carrier
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H:=C.normalized_translation_mem
  have hpres : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1).val '' E=E:=
    (D.nielsenConjugate C.normalizer).image_eq ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      1,hT⟩
  have hE : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc E:=D.isDisc.image C.normalizer
  have hsub : _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere C.height⊆E:=by
    rw [←C.disc_eq]
    exact image_mono S.subset_domain
  obtain ⟨h,hupper|hlower⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.parabolicTranslationDisc_eq_halfPlane hE hpres
  · refine ⟨h,hupper,?_⟩
    by_contra hh
    have hlt : C.height<h:=lt_of_not_ge hh
    let z : ℂ:=⟨0,(C.height+h)/2⟩
    have hz : (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere C.height:=
      ⟨z,by change C.height<(C.height+h)/2;linarith,rfl⟩
    have hm:=hsub hz
    rw [hupper] at hm
    obtain ⟨w,hw,hwe⟩:=hm
    have hwz : w=z:=OnePoint.coe_injective hwe
    rw [hwz] at hw
    change h<(C.height+h)/2 at hw
    linarith
  · let z : ℂ:=⟨0,max h C.height+1⟩
    have hz : (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere C.height:=by
      refine ⟨z,?_,rfl⟩
      change C.height<max h C.height+1
      linarith [le_max_right h C.height]
    have hm:=hsub hz
    rw [hlower] at hm
    obtain ⟨w,hw,hwe⟩:=hm
    have hwz : w=z:=OnePoint.coe_injective hwe
    rw [hwz] at hw
    change max h C.height+1<h at hw
    linarith [le_max_left h C.height]

/-- The whole original disc closure, in any genuine cusp chart, has a uniform lower imaginary-coordinate bound at every actual finite point. -/
theorem cuspNormalization_original_closure_im_bounded_below {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain} {p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p) :
    ∃h : ℝ,∀z∈closure D.carrier,∀w : ℂ,C.normalizer.val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→h≤w.im := by
  obtain ⟨h,he,_hh⟩:=cuspNormalization_original_domain_upper D C
  refine ⟨h,?_⟩
  intro z hz w hw
  have him : (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h):=by
    rw [←he]
    change (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph C.normalizer) '' D.carrier)
    rw [←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph C.normalizer).image_closure]
    exact ⟨z,hz,hw⟩
  have hpre : w∈((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' closure (((↑) :
    ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {w : ℂ | h<w.im}):=him
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.onePoint_coe_preimage_closure_image] at hpre
  exact closure_minimal (fun z hz=>hz.le)
    (isClosed_le continuous_const Complex.continuous_im) hpre

/-- A genuine cusp chart can be shifted by a purely imaginary translation to a genuine whole-disc upper-half-plane normalizer, without changing any finite real coordinate. -/
theorem cuspNormalization_upperHalfPlane_chart {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain} {p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p) :
    ∃h : ℝ,∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧ q.val p=∞ ∧
      ∀z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,∀w : ℂ,C.normalizer.val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        q.val z=((w-(h:ℂ)*Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨h,he,_hh⟩:=cuspNormalization_original_domain_upper D C
  let q:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)*C.normalizer
  refine ⟨h,q,?_,?_,?_⟩
  · change ((fun z=>(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)).val
    (C.normalizer.val z)) '' D.carrier)=_
    rw [←image_image,he]
    exact vertical_cusp_shift_image h
  · change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
    (-(h:ℂ)*Complex.I)).val (C.normalizer.val p)=∞
    rw [C.cusp_eq,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]
  · intro z w hw
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      (-(h:ℂ)*Complex.I)).val (C.normalizer.val z)=_
    rw [hw,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring

/-- The actual closed finite rectangle determined by real and imaginary coordinate bounds is compact in the complex plane. -/
theorem cusp_coordinate_rectangle_isCompact (M h t : ℝ) :
    IsCompact {z : ℂ | |z.re|≤M∧h≤z.im∧z.im≤t} := by
  let e:=Complex.equivRealProdCLM.toHomeomorph
  have he : {z : ℂ | |z.re|≤M∧h≤z.im∧z.im≤t}=
      e.symm '' (Icc (-M) M×ˢIcc h t):=by
    ext z
    rw [e.symm.image_eq_preimage_symm]
    change (|z.re|≤M∧h≤z.im∧z.im≤t)↔((-M≤z.re∧z.re≤M)∧h≤z.im∧z.im≤t)
    rw [abs_le]
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image e.symm.continuous

/-- Real-coordinate boundedness and a lower imaginary bound force actual sphere neighborhoods of infinity to enter every genuine uniform-height cusp tail on the given set. -/
theorem cusp_height_tail_sphere_neighborhood (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (q
  : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hqp : q.val p=∞) (M h : ℝ)
    (hb : ∀z∈K,∀w : ℂ,q.val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→|w.re|≤M∧h≤w.im)
    (t : ℝ) :
    ∃U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsOpen U∧p∈U∧∀z∈K∩U,
      q.val z=∞∨∃w : ℂ,t<w.im∧q.val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  let R : Set ℂ:={z | |z.re|≤M∧h≤z.im∧z.im≤t}
  have hcompact : IsCompact (((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' R):=
    (cusp_coordinate_rectangle_isCompact M h t).image OnePoint.continuous_coe
  let U:=q.val ⁻¹' (((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' R)ᶜ
  refine ⟨U,hcompact.isClosed.isOpen_compl.preimage
    (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary q),?_,?_⟩
  · change q.val p∉((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' R
    rw [hqp]
    rintro ⟨w,_hw,he⟩
    exact OnePoint.coe_ne_infty w he
  · intro z hz
    by_cases hinf : q.val z=∞
    · exact Or.inl hinf
    · obtain ⟨w,hw⟩:=OnePoint.ne_infty_iff_exists.mp hinf
      have hwe : q.val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=hw.symm
      refine Or.inr ⟨w,?_,hwe⟩
      by_contra hn
      have hbound:=hb z hz.1 w hwe
      have hwR : w∈R:=⟨hbound.1,hbound.2,le_of_not_gt hn⟩
      exact hz.2 ⟨w,hwR,hw⟩

end LowDimensionalTopology.Geometry.Fuchsian
