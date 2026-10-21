/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedSides
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

theorem modular_re_le_hConvex (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | z.re≤a} := by
  have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (closure (UpperHalfPlane.re ⁻¹' Iio a)):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex a).closure
  rw [←UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,
    closure_Iio] at h
  exact h

theorem modular_re_ge_hConvex (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | a≤z.re} := by
  have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (closure (UpperHalfPlane.re ⁻¹' Ioi a)):=
    (modular_re_gt_hConvex a).closure
  rw [←UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,
    closure_Ioi] at h
  exact h

def modularUnitGeodesicArc (c l u : ℝ) : Set ℍ:=
  {z | Complex.normSq ((z:ℂ)-(c:ℂ))=1 ∧ l≤z.re ∧ z.re≤u}

theorem modularUnitGeodesicArc_in_circle (c l u : ℝ) :
    modularUnitGeodesicArc c l u⊆(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c 1 (by norm_num)).carrier := by
  intro z hz
  have hn:=hz.1
  rw [Complex.normSq_eq_norm_sq] at hn
  change ‖(z:ℂ)-(c:ℂ)‖=1
  nlinarith [norm_nonneg ((z:ℂ)-(c:ℂ))]

theorem modularUnitGeodesicArc_hConvex
    (c l u : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularUnitGeodesicArc c l u) := by
  intro z hz w hw t ht
  have hcircle:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c 1 (by norm_num)).hConvex
    z (modularUnitGeodesicArc_in_circle c l u hz) w (modularUnitGeodesicArc_in_circle c l u hw) ht
  have hn : Complex.normSq ((t:ℂ)-(c:ℂ))=1:=by
    change ‖(t:ℂ)-(c:ℂ)‖=1 at hcircle
    rw [Complex.normSq_eq_norm_sq,hcircle]
    norm_num
  exact ⟨hn,modular_re_ge_hConvex l z hz.2.1 w hw.2.1 ht,
    modular_re_le_hConvex u z hz.2.2 w hw.2.2 ht⟩

theorem modular_shifted_closed_hConvex
    (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularClosedShiftedPolygon a) := by
  rw [←modularShiftedPolygon_closure]
  exact (modularShiftedPolygon_hConvex a).closure

theorem modular_shifted_sides_hConvex (a : ℝ) (ha : a<0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedLeftSide a) ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedRightSide a) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedSelfArc a) ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedPairedArc a) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedRightArc a) ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedSelfArcLeft a) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularShiftedSelfArcRight a) := by
  have hv (x : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularClosedShiftedPolygon a∩(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).carrier):=by
    intro z hz w hw t ht
    exact ⟨modular_shifted_closed_hConvex a z hz.1 w hw.1 ht,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).hConvex z hz.2 w hw.2 ht⟩
  have heS : modularShiftedSelfArc a=modularUnitGeodesicArc 0 a (-a):=by
    ext z
    simp only [modularShiftedSelfArc,modularUnitGeodesicArc,Complex.ofReal_zero,sub_zero]
  have heP : modularShiftedPairedArc a=modularUnitGeodesicArc 0 (-a) (1/2):=by
    ext z
    simp only [modularShiftedPairedArc,modularUnitGeodesicArc,Complex.ofReal_zero,sub_zero]
  have heC : modularShiftedRightArc a=modularUnitGeodesicArc 1 (1/2) (a+1):=by
    simp only [modularShiftedRightArc,modularUnitGeodesicArc,Complex.ofReal_one]
  have heA : modularShiftedSelfArcLeft a=modularUnitGeodesicArc 0 a 0:=by
    ext z
    simp only [modularShiftedSelfArcLeft,modularShiftedSelfArc,modularUnitGeodesicArc,
      Complex.ofReal_zero,sub_zero,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hN,hl,_⟩,hr⟩
      exact ⟨hN,hl,hr⟩
    · rintro ⟨hN,hl,hr⟩
      exact ⟨⟨hN,hl,by linarith⟩,hr⟩
  have heB : modularShiftedSelfArcRight a=modularUnitGeodesicArc 0 0 (-a):=by
    ext z
    simp only [modularShiftedSelfArcRight,modularShiftedSelfArc,modularUnitGeodesicArc,
      Complex.ofReal_zero,sub_zero,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hN,_,hr⟩,hl⟩
      exact ⟨hN,hl,hr⟩
    · rintro ⟨hN,hl,hr⟩
      exact ⟨⟨hN,by linarith,hr⟩,hl⟩
  exact ⟨hv a,hv (a+1),heS ▸ modularUnitGeodesicArc_hConvex 0 a (-a),
    heP ▸ modularUnitGeodesicArc_hConvex 0 (-a) (1/2),
    heC ▸ modularUnitGeodesicArc_hConvex 1 (1/2) (a+1),
    heA ▸ modularUnitGeodesicArc_hConvex 0 a 0,heB ▸ modularUnitGeodesicArc_hConvex 0 0 (-a)⟩

theorem modular_shifted_sides_nontrivial (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (modularShiftedLeftSide a).Nontrivial ∧ (modularShiftedRightSide a).Nontrivial ∧
    (modularShiftedSelfArc a).Nontrivial ∧ (modularShiftedPairedArc a).Nontrivial ∧
    (modularShiftedRightArc a).Nontrivial ∧ (modularShiftedSelfArcLeft a).Nontrivial ∧
    (modularShiftedSelfArcRight a).Nontrivial := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hc:=modular_cut_cycle_points_closed a ha₁ ha₂
  have hS:=modular_S_unit_coordinates w hp.2.1
  have hSr : (ModularGroup.S•w).re=a:=by rw [hS.2,hp.1];ring
  have hTr : ((ModularGroup.T*ModularGroup.S)•w).re=a+1:=by
    rw [mul_smul,(modular_T_coordinates _).1,hSr]
  have hwS : w∈modularShiftedSelfArc a:=⟨hp.2.1,by linarith [hp.1],hp.1.le⟩
  have hwP : w∈modularShiftedPairedArc a:=⟨hp.2.1,hp.1.ge,hp.2.2.2.le⟩
  have hSS : ModularGroup.S•w∈modularShiftedSelfArc a:=modular_S_shifted_selfArc a w hwS
  have hSA : ModularGroup.S•w∈modularShiftedSelfArcLeft a:=⟨hSS,by change (ModularGroup.S•w).re≤0;rw [hSr];exact ha₂.le⟩
  have hwB : w∈modularShiftedSelfArcRight a:=⟨hwS,hp.2.2.1.le⟩
  have hiS : UpperHalfPlane.I∈modularShiftedSelfArc a:=by
    refine ⟨by norm_num,?_,?_⟩ <;> norm_num <;> linarith
  have hiA : UpperHalfPlane.I∈modularShiftedSelfArcLeft a:=⟨hiS,by norm_num⟩
  have hiB : UpperHalfPlane.I∈modularShiftedSelfArcRight a:=⟨hiS,by norm_num⟩
  have hζP : modularZeta∈modularShiftedPairedArc a:=
    ⟨modularZeta_properties.2.1,by rw [modularZeta_properties.1];linarith,modularZeta_properties.1.le⟩
  have hζC : modularZeta∈modularShiftedRightArc a:=by
    refine ⟨?_,modularZeta_properties.1.ge,?_⟩
    · rw [modular_normSq_sub_one,modularZeta_properties.2.1,modularZeta_properties.1]
      norm_num
    · rw [modularZeta_properties.1]
      linarith
  have hTC : (ModularGroup.T*ModularGroup.S)•w∈modularShiftedRightArc a:=
    modular_TS_shifted_pairedArc a w hwP
  have hiw : UpperHalfPlane.I≠w:=by
    intro he
    have hh:=congrArg UpperHalfPlane.re he
    rw [UpperHalfPlane.I_re,hp.1] at hh
    linarith
  obtain ⟨l,hlr,hlc,hln,_⟩:=modular_shifted_vertical_witness a a (Or.inl rfl)
  obtain ⟨r,hrr,hrc,_,hrn'⟩:=modular_shifted_vertical_witness a (a+1) (Or.inr rfl)
  refine ⟨⟨l,⟨hlc,hlr⟩,ModularGroup.S•w,⟨hc.2.1,hSr⟩,?_⟩,
    ⟨r,⟨hrc,hrr⟩,(ModularGroup.T*ModularGroup.S)•w,⟨hc.2.2,hTr⟩,?_⟩,
    ⟨UpperHalfPlane.I,hiS,w,hwS,hiw⟩,⟨w,hwP,modularZeta,hζP,?_⟩,
    ⟨(ModularGroup.T*ModularGroup.S)•w,hTC,modularZeta,hζC,?_⟩,
    ⟨ModularGroup.S•w,hSA,UpperHalfPlane.I,hiA,?_⟩,
    ⟨UpperHalfPlane.I,hiB,w,hwB,hiw⟩⟩
  · intro he
    have hh:=congrArg (fun z : ℍ=>Complex.normSq (z:ℂ)) he
    rw [hS.1] at hh
    exact (ne_of_gt hln) hh
  · intro he
    have hh:=congrArg (fun z : ℍ=>Complex.normSq ((z:ℂ)-1)) he
    rw [modular_TS_normSq_sub_one,hS.1] at hh
    exact (ne_of_gt hrn') hh
  · intro he
    have hh:=congrArg UpperHalfPlane.re he
    rw [hp.1,modularZeta_properties.1] at hh
    linarith
  · intro he
    have hh:=congrArg UpperHalfPlane.re he
    rw [hTr,modularZeta_properties.1] at hh
    linarith
  · intro he
    have hh:=congrArg UpperHalfPlane.re he
    rw [hSr,UpperHalfPlane.I_re] at hh
    linarith

end LowDimensionalTopology.Geometry.Fuchsian
