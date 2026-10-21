/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularDirichlet
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian

def modularLeftSide : Set ℍ:={z | z.re= -(1/2) ∧ 1≤Complex.normSq (z:ℂ)}
def modularRightSide : Set ℍ:={z | z.re=1/2 ∧ 1≤Complex.normSq (z:ℂ)}
def modularRoundSide : Set ℍ:={z | Complex.normSq (z:ℂ)=1 ∧ |z.re|≤1/2}
def modularLeftRoundSide : Set ℍ:={z | z∈modularRoundSide ∧ z.re≤0}
def modularRightRoundSide : Set ℍ:={z | z∈modularRoundSide ∧ 0≤z.re}

theorem modular_frontier_eq_sides :
    frontier ModularGroup.fdo=modularLeftSide∪modularRightSide∪modularRoundSide := by
  rw [ModularGroup.isOpen_fdo.frontier_eq,←ModularGroup.fd_eq_closure_fdo]
  ext z
  constructor
  · rintro ⟨⟨hn,hx⟩,hnot⟩
    by_cases he : Complex.normSq (z:ℂ)=1
    · exact Or.inr ⟨he,hx⟩
    · have hnorm : 1<Complex.normSq (z:ℂ):=lt_of_le_of_ne hn (Ne.symm he)
      have hx' : |z.re|=1/2:=le_antisymm hx (not_lt.mp (fun h=>hnot ⟨hnorm,h⟩))
      rcases abs_eq (by norm_num : 0≤(1/2:ℝ)) |>.mp hx' with h|h
      · exact Or.inl (Or.inr ⟨h,hn⟩)
      · exact Or.inl (Or.inl ⟨h,hn⟩)
  · rintro ((⟨h,hN⟩|⟨h,hN⟩)|⟨hN,h⟩)
    · refine ⟨⟨hN,by rw [h];norm_num⟩,?_⟩
      intro hf
      have hh:=hf.2
      rw [h] at hh
      norm_num at hh
    · refine ⟨⟨hN,by rw [h];norm_num⟩,?_⟩
      intro hf
      have hh:=hf.2
      rw [h] at hh
      norm_num at hh
    · exact ⟨⟨hN.ge,h⟩,fun hf=>(ne_of_lt hf.1) hN.symm⟩

theorem modular_T_coordinates (z : ℍ) :
    (ModularGroup.T•z).re=z.re+1 ∧
    Complex.normSq ((ModularGroup.T•z:ℍ):ℂ)=Complex.normSq (z:ℂ)+2*z.re+1 := by
  rw [UpperHalfPlane.modular_T_smul]
  constructor
  · simp [add_comm]
  · simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
      UpperHalfPlane.vadd_re,UpperHalfPlane.vadd_im]
    ring

theorem modular_T_leftSide (z : ℍ) :
    ModularGroup.T•z∈modularRightSide ↔ z∈modularLeftSide := by
  have hc:=modular_T_coordinates z
  constructor
  · rintro ⟨hr,hn⟩
    have hz : z.re= -(1/2):=by linarith [hc.1]
    exact ⟨hz,by rw [hc.2] at hn;linarith⟩
  · rintro ⟨hr,hn⟩
    exact ⟨by linarith [hc.1],by rw [hc.2];linarith⟩

theorem modular_T_side_pairing :
    (fun z : ℍ=>ModularGroup.T•z) '' modularLeftSide=modularRightSide := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (modular_T_leftSide x).mpr hx
  · intro hz
    refine ⟨ModularGroup.T⁻¹•z,?_,smul_inv_smul _ _⟩
    apply (modular_T_leftSide _).mp
    simpa only [smul_inv_smul] using hz

theorem modular_S_unit_circle (z : ℍ) (hz : Complex.normSq (z:ℂ)=1) :
    ((ModularGroup.S•z:ℍ):ℂ)= -conj (z:ℂ) := by
  have hn : ‖(z:ℂ)‖=1:=by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg (z:ℂ)]
  rw [UpperHalfPlane.modular_S_smul]
  change (-(z:ℂ))⁻¹= -conj (z:ℂ)
  rw [inv_neg,Complex.inv_eq_conj hn]

theorem modular_S_roundSide (z : ℍ) (hz : z∈modularRoundSide) :
    ModularGroup.S•z∈modularRoundSide := by
  have hc:=modular_S_unit_circle z hz.1
  constructor
  · rw [hc,Complex.normSq_neg,Complex.normSq_conj]
    exact hz.1
  · change |(((ModularGroup.S•z:ℍ):ℂ)).re|≤1/2
    rw [hc,Complex.neg_re,Complex.conj_re,abs_neg]
    exact hz.2

theorem modular_S_involutive (z : ℍ) : ModularGroup.S•(ModularGroup.S•z)=z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul,UpperHalfPlane.modular_S_smul]
  change (-(-(z:ℂ))⁻¹)⁻¹=(z:ℂ)
  simp

theorem modular_S_round_pairing :
    (fun z : ℍ=>ModularGroup.S•z) '' modularRoundSide=modularRoundSide := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact modular_S_roundSide x hx
  · intro hz
    exact ⟨ModularGroup.S•z,modular_S_roundSide z hz,modular_S_involutive z⟩

theorem modular_round_split : modularRoundSide=modularLeftRoundSide∪modularRightRoundSide := by
  ext z
  exact ⟨fun hz=>by rcases le_total z.re 0 with h|h;exact Or.inl ⟨hz,h⟩;exact Or.inr ⟨hz,h⟩,
    fun hz=>by rcases hz with h|h;exact h.1;exact h.1⟩

theorem modular_S_split_pairing :
    (fun z : ℍ=>ModularGroup.S•z) '' modularLeftRoundSide=modularRightRoundSide := by
  have hm (z : ℍ) (hz : z∈modularRoundSide) : (ModularGroup.S•z).re= -z.re:=by
    change (((ModularGroup.S•z:ℍ):ℂ)).re= _
    rw [modular_S_unit_circle z hz.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re]
  ext z
  constructor
  · rintro ⟨x,⟨hx,hr⟩,rfl⟩
    exact ⟨modular_S_roundSide x hx,by rw [hm x hx];linarith⟩
  · rintro ⟨hz,hr⟩
    exact ⟨ModularGroup.S•z,⟨modular_S_roundSide z hz,by rw [hm z hz];linarith⟩,modular_S_involutive z⟩

theorem modular_split_sides_intersection : modularLeftRoundSide∩modularRightRoundSide={UpperHalfPlane.I} := by
  ext z
  constructor
  · rintro ⟨⟨hz,hl⟩,⟨_,hr⟩⟩
    have hre : z.re=0:=by linarith
    have him : z.im=1:=by
      have hh:=hz.1
      rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,hre] at hh
      nlinarith [z.im_pos]
    apply Set.mem_singleton_iff.mpr
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa only [UpperHalfPlane.coe_re,UpperHalfPlane.I_re] using hre
    · simpa only [UpperHalfPlane.coe_im,UpperHalfPlane.I_im] using him
  · rintro rfl
    norm_num [modularLeftRoundSide,modularRightRoundSide,modularRoundSide]


theorem modular_open_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex ModularGroup.fdo := by
  rw [←modular_dirichlet_domain 2 (by norm_num)]
  intro z hz w hw u hu g hg
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_closer_halfPlane_convex _ _) z (hz g hg) w (hw g hg) hu

theorem modular_closed_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex ModularGroup.fd := by
  rw [ModularGroup.fd_eq_closure_fdo]
  exact modular_open_hConvex.closure

theorem modular_leftSide_eq_closed_inter_line :
    modularLeftSide=ModularGroup.fd∩(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-(1/2))).carrier := by
  ext z
  constructor
  · rintro ⟨hre,hnorm⟩
    exact ⟨⟨hnorm,by rw [hre];norm_num⟩,hre⟩
  · rintro ⟨hD,hre⟩
    exact ⟨hre,hD.1⟩

theorem modular_rightSide_eq_closed_inter_line :
    modularRightSide=ModularGroup.fd∩(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (1/2)).carrier := by
  ext z
  constructor
  · rintro ⟨hre,hnorm⟩
    exact ⟨⟨hnorm,by rw [hre];norm_num⟩,hre⟩
  · rintro ⟨hD,hre⟩
    exact ⟨hre,hD.1⟩

theorem modular_roundSide_eq_closed_inter_line :
    modularRoundSide=ModularGroup.fd∩(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
  ext z
  have hn : Complex.normSq (z:ℂ)=1 ↔ ‖(z:ℂ)‖=1:=by
    rw [Complex.normSq_eq_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (z:ℂ)]
  constructor
  · rintro ⟨hN,hre⟩
    refine ⟨⟨hN.ge,hre⟩,?_⟩
    change ‖(z:ℂ)-(0:ℂ)‖=1
    simpa only [sub_zero] using hn.mp hN
  · rintro ⟨hD,hline⟩
    have hnorm : ‖(z:ℂ)‖=1:=by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier,Complex.ofReal_zero,sub_zero,Set.mem_ofPred_eq] using hline
    exact ⟨hn.mpr hnorm,hD.2⟩

theorem modular_geodesic_sides_convex :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex modularLeftSide ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex modularRightSide ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex modularRoundSide := by
  have hm (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (ModularGroup.fd∩L.carrier):=by
    intro z hz w hw u hu
    exact ⟨modular_closed_hConvex z hz.1 w hw.1 hu,L.hConvex z hz.2 w hw.2 hu⟩
  exact ⟨modular_leftSide_eq_closed_inter_line ▸ hm _,
    modular_rightSide_eq_closed_inter_line ▸ hm _,modular_roundSide_eq_closed_inter_line ▸ hm _⟩


def modularRoundPoint (x : ℝ) (hx : |x|<1) : ℍ:=
  ⟨⟨x,Real.sqrt (1-x^2)⟩,by
    apply Real.sqrt_pos.mpr
    have hh:=abs_lt.mp hx
    nlinarith⟩

theorem modularRoundPoint_norm (x : ℝ) (hx : |x|<1) :
    Complex.normSq (modularRoundPoint x hx:ℂ)=1 := by
  have hh:=abs_lt.mp hx
  have hp : 0≤1-x^2:=by nlinarith
  change x*x+Real.sqrt (1-x^2)*Real.sqrt (1-x^2)=1
  nlinarith [Real.sq_sqrt hp]

theorem modular_vertical_sides_distinct : modularLeftSide≠modularRightSide := by
  intro he
  let z:=modularRoundPoint (-(1/2)) (by norm_num)
  have hz : z∈modularLeftSide:=⟨rfl,(modularRoundPoint_norm _ _).ge⟩
  have hr : z∈modularRightSide:=he ▸ hz
  have hh:=hr.1
  change -(1/2:ℝ)=1/2 at hh
  norm_num at hh

theorem modular_leftSide_ne_of_I_mem (S : Set ℍ) (hS : UpperHalfPlane.I∈S) :
    modularLeftSide≠S := by
  intro he
  have hnot : UpperHalfPlane.I∉modularLeftSide:=by norm_num [modularLeftSide]
  exact hnot (he.symm ▸ hS)

theorem modular_rightSide_ne_of_I_mem (S : Set ℍ) (hS : UpperHalfPlane.I∈S) :
    modularRightSide≠S := by
  intro he
  have hnot : UpperHalfPlane.I∉modularRightSide:=by norm_num [modularRightSide]
  exact hnot (he.symm ▸ hS)

theorem modular_round_sides_distinct : modularLeftRoundSide≠modularRightRoundSide := by
  intro he
  let z:=modularRoundPoint (-(1/4)) (by norm_num)
  have hz : z∈modularLeftRoundSide:=⟨⟨modularRoundPoint_norm _ _,by change |(-(1/4):ℝ)|≤1/2;norm_num⟩,by change -(1/4:ℝ)≤0;norm_num⟩
  have hr : z∈modularRightRoundSide:=he ▸ hz
  have hh:=hr.2
  change 0≤-(1/4:ℝ) at hh
  norm_num at hh

theorem modular_three_sides_card :
    ({modularLeftSide,modularRightSide,modularRoundSide} : Finset (Set ℍ)).card=3 := by
  classical
  have hl:=modular_leftSide_ne_of_I_mem modularRoundSide (by norm_num [modularRoundSide])
  have hr:=modular_rightSide_ne_of_I_mem modularRoundSide (by norm_num [modularRoundSide])
  simp [modular_vertical_sides_distinct,hl,hr]

theorem modular_four_sides_card :
    ({modularLeftSide,modularRightSide,modularLeftRoundSide,modularRightRoundSide} : Finset (Set ℍ)).card=4 := by
  classical
  have hiL : UpperHalfPlane.I∈modularLeftRoundSide:=by norm_num [modularLeftRoundSide,modularRoundSide]
  have hiR : UpperHalfPlane.I∈modularRightRoundSide:=by norm_num [modularRightRoundSide,modularRoundSide]
  have hll:=modular_leftSide_ne_of_I_mem _ hiL
  have hlr:=modular_leftSide_ne_of_I_mem _ hiR
  have hrl:=modular_rightSide_ne_of_I_mem _ hiL
  have hrr:=modular_rightSide_ne_of_I_mem _ hiR
  simp [modular_vertical_sides_distinct,modular_round_sides_distinct,hll,hlr,hrl,hrr]

theorem modular_frontier_eq_four_sides :
    frontier ModularGroup.fdo=modularLeftSide∪modularRightSide∪modularLeftRoundSide∪modularRightRoundSide := by
  simp only [modular_frontier_eq_sides,modular_round_split,union_assoc]


theorem modular_S_reverse_split_pairing :
    (fun z : ℍ=>ModularGroup.S•z) '' modularRightRoundSide=modularLeftRoundSide := by
  rw [←modular_S_split_pairing,Set.image_image]
  have hf : (fun z : ℍ=>ModularGroup.S•(ModularGroup.S•z))=id:=funext modular_S_involutive
  change (fun z : ℍ=>ModularGroup.S•(ModularGroup.S•z)) '' modularLeftRoundSide=modularLeftRoundSide
  rw [hf,Set.image_id]

theorem modular_I_fixed_order_two :
    modularNativeHom ModularGroup.S UpperHalfPlane.I=UpperHalfPlane.I ∧
      modularNativeHom ModularGroup.S≠1 ∧ (modularNativeHom ModularGroup.S)^2=1 := by
  refine ⟨?_,(modularNativeHom_ne_one_iff _).mpr (by constructor <;> decide),?_⟩
  · rw [modularNativeHom_apply]
    apply UpperHalfPlane.ext
    rw [modular_S_unit_circle _ (by norm_num)]
    norm_num
  · apply IsometryEquiv.ext
    intro z
    change modularNativeHom ModularGroup.S (modularNativeHom ModularGroup.S z)=z
    rw [modularNativeHom_apply,modularNativeHom_apply,modular_S_involutive]

/-- The literal two-circle exterior in the shifted unit strip. -/
def modularShiftedPolygon (a : ℝ) : Set ℍ:=
  {z | a<z.re ∧ z.re<a+1 ∧ 1<Complex.normSq (z:ℂ) ∧ 1<Complex.normSq ((z:ℂ)-1)}

theorem modularShiftedPolygon_left (a : ℝ) (ha : -(1/2)<a) (z : ℍ) (hz : z.re<1/2) :
    z∈modularShiftedPolygon a ↔ z∈ModularGroup.fdo ∧ a<z.re := by
  have hn : Complex.normSq ((z:ℂ)-1)=Complex.normSq (z:ℂ)+1-2*z.re:=by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
      Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero]
    ring
  constructor
  · rintro ⟨h₁,_h₂,h₃,_h₄⟩
    exact ⟨⟨h₃,abs_lt.mpr ⟨by linarith,by linarith⟩⟩,h₁⟩
  · rintro ⟨hD,h₁⟩
    refine ⟨h₁,by linarith,hD.1,?_⟩
    rw [hn]
    linarith [hD.1]

theorem modularShiftedPolygon_right (a : ℝ) (ha : a<0) (z : ℍ) (hz : 1/2<z.re) :
    z∈modularShiftedPolygon a ↔ ModularGroup.T⁻¹•z∈ModularGroup.fdo ∧ z.re<a+1 := by
  have hc : ((ModularGroup.T⁻¹•z:ℍ):ℂ)=(z:ℂ)-1:=by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    norm_num [ModularGroup.T,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    ring
  have hre : (ModularGroup.T⁻¹•z).re=z.re-1:=by
    change (((ModularGroup.T⁻¹•z:ℍ):ℂ)).re=_
    rw [hc]
    simp
  have hn : Complex.normSq ((z:ℂ)-1)=Complex.normSq (z:ℂ)+1-2*z.re:=by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
      Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero]
    ring
  constructor
  · rintro ⟨_h₁,h₂,_h₃,h₄⟩
    refine ⟨⟨?_,?_⟩,h₂⟩
    · simpa only [hc] using h₄
    · rw [hre]
      exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · rintro ⟨hD,h₂⟩
    have hnorm : 1<Complex.normSq ((z:ℂ)-1):=by simpa only [hc] using hD.1
    refine ⟨by linarith,h₂,?_,hnorm⟩
    rw [hn] at hnorm
    linarith

theorem modularShiftedPolygon_join (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℍ) (hz : z.re=1/2) :
    z∈modularShiftedPolygon a ↔ 3/4<z.im^2 := by
  have hnorm : Complex.normSq (z:ℂ)=1/4+z.im^2:=by
    rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,hz]
    ring
  have hnorm' : Complex.normSq ((z:ℂ)-1)=1/4+z.im^2:=by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
      Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero,hz]
    ring
  constructor
  · rintro ⟨_,_,h,_⟩
    rw [hnorm] at h
    linarith
  · intro h
    exact ⟨by linarith,by linarith,by rw [hnorm];linarith,by rw [hnorm'];linarith⟩

end LowDimensionalTopology.Geometry.Fuchsian
