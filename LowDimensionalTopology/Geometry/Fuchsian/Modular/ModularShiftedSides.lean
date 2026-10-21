/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Topology ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian

def modularShiftedLeftSide (a : ℝ) : Set ℍ:=modularClosedShiftedPolygon a∩{z | z.re=a}
def modularShiftedRightSide (a : ℝ) : Set ℍ:=modularClosedShiftedPolygon a∩{z | z.re=a+1}
def modularShiftedLeftArc (a : ℝ) : Set ℍ:=
  {z | Complex.normSq (z:ℂ)=1 ∧ a≤z.re ∧ z.re≤1/2}
def modularShiftedRightArc (a : ℝ) : Set ℍ:=
  {z | Complex.normSq ((z:ℂ)-1)=1 ∧ 1/2≤z.re ∧ z.re≤a+1}
def modularShiftedSelfArc (a : ℝ) : Set ℍ:=
  {z | Complex.normSq (z:ℂ)=1 ∧ a≤z.re ∧ z.re≤ -a}
def modularShiftedPairedArc (a : ℝ) : Set ℍ:=
  {z | Complex.normSq (z:ℂ)=1 ∧ -a≤z.re ∧ z.re≤1/2}
def modularShiftedSelfArcLeft (a : ℝ) : Set ℍ:=modularShiftedSelfArc a∩{z | z.re≤0}
def modularShiftedSelfArcRight (a : ℝ) : Set ℍ:=modularShiftedSelfArc a∩{z | 0≤z.re}

theorem modular_shifted_left_arc_closed (a : ℝ) (ha : -(1/2)<a) (z : ℍ)
    (hz : z∈modularShiftedLeftArc a) : z∈modularClosedShiftedPolygon a := by
  refine ⟨hz.2.1,by linarith [hz.2.2],hz.1.ge,?_⟩
  rw [modular_normSq_sub_one,hz.1]
  linarith [hz.2.2]

theorem modular_shifted_right_arc_closed (a : ℝ) (ha : a<0) (z : ℍ)
    (hz : z∈modularShiftedRightArc a) : z∈modularClosedShiftedPolygon a := by
  have hn:=hz.1
  rw [modular_normSq_sub_one] at hn
  exact ⟨by linarith [hz.2.1],hz.2.2,by linarith [hz.2.1],hz.1.ge⟩

theorem modular_shifted_frontier_four_carriers (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    frontier (modularShiftedPolygon a)=modularShiftedLeftSide a∪modularShiftedRightSide a∪
      modularShiftedLeftArc a∪modularShiftedRightArc a := by
  rw [(modularShiftedPolygon_isOpen a).frontier_eq,modularShiftedPolygon_closure]
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    by_cases hl : z.re=a
    · exact Or.inl (Or.inl (Or.inl ⟨hz,hl⟩))
    by_cases hr : z.re=a+1
    · exact Or.inl (Or.inl (Or.inr ⟨hz,hr⟩))
    by_cases hN : Complex.normSq (z:ℂ)=1
    · apply Or.inl;apply Or.inr
      refine ⟨hN,hz.1,?_⟩
      have hh:=hz.2.2.2
      rw [modular_normSq_sub_one,hN] at hh
      linarith
    have hN' : Complex.normSq ((z:ℂ)-1)=1:=by
      by_contra hh
      exact hn ⟨lt_of_le_of_ne hz.1 (Ne.symm hl),lt_of_le_of_ne hz.2.1 hr,
        lt_of_le_of_ne hz.2.2.1 (Ne.symm hN),lt_of_le_of_ne hz.2.2.2 (Ne.symm hh)⟩
    apply Or.inr
    refine ⟨hN',?_,hz.2.1⟩
    rw [modular_normSq_sub_one] at hN'
    linarith [hz.2.2.1]
  · rintro (((⟨hz,hl⟩|⟨hz,hr⟩)|hz)|hz)
    · refine ⟨hz,fun hh=>?_⟩
      change z.re=a at hl
      linarith [hh.1]
    · refine ⟨hz,fun hh=>?_⟩
      change z.re=a+1 at hr
      linarith [hh.2.1]
    · exact ⟨modular_shifted_left_arc_closed a ha₁ z hz,fun hh=>by linarith [hh.2.2.1,hz.1]⟩
    · exact ⟨modular_shifted_right_arc_closed a ha₂ z hz,fun hh=>by linarith [hh.2.2.2,hz.1]⟩

theorem modular_shifted_left_arc_split (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularShiftedLeftArc a=modularShiftedSelfArc a∪modularShiftedPairedArc a := by
  ext z
  constructor
  · intro hz
    rcases le_total z.re (-a) with h|h
    · exact Or.inl ⟨hz.1,hz.2.1,h⟩
    · exact Or.inr ⟨hz.1,h,hz.2.2⟩
  · rintro (hz|hz)
    · exact ⟨hz.1,hz.2.1,by linarith [hz.2.2]⟩
    · exact ⟨hz.1,by linarith [hz.2.1],hz.2.2⟩

theorem modular_shifted_self_arc_split (a : ℝ) :
    modularShiftedSelfArc a=modularShiftedSelfArcLeft a∪modularShiftedSelfArcRight a := by
  ext z
  exact ⟨fun h=>(le_total z.re 0).elim (fun hl=>Or.inl ⟨h,hl⟩) (fun hr=>Or.inr ⟨h,hr⟩),
    fun h=>h.elim And.left And.left⟩

theorem modular_shifted_frontier_five_sides (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    frontier (modularShiftedPolygon a)=modularShiftedLeftSide a∪modularShiftedRightSide a∪
      modularShiftedSelfArc a∪modularShiftedPairedArc a∪modularShiftedRightArc a := by
  rw [modular_shifted_frontier_four_carriers a ha₁ ha₂,modular_shifted_left_arc_split a ha₁ ha₂]
  ext z
  simp only [Set.mem_union]
  tauto

theorem modular_shifted_frontier_six_sides (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    frontier (modularShiftedPolygon a)=modularShiftedLeftSide a∪modularShiftedRightSide a∪
      modularShiftedSelfArcLeft a∪modularShiftedSelfArcRight a∪modularShiftedPairedArc a∪
      modularShiftedRightArc a := by
  rw [modular_shifted_frontier_five_sides a ha₁ ha₂,modular_shifted_self_arc_split]
  ext z
  simp only [Set.mem_union]
  tauto

theorem modular_T_inv_shifted_rightSide (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) (z : ℍ) :
    ModularGroup.T⁻¹•z∈modularShiftedLeftSide a ↔ z∈modularShiftedRightSide a := by
  have hc:=modular_T_coordinates (ModularGroup.T⁻¹•z)
  rw [smul_inv_smul] at hc
  have hN : Complex.normSq ((ModularGroup.T⁻¹•z:ℍ):ℂ)=Complex.normSq ((z:ℂ)-1):=by rw [modular_T_inv_coe]
  constructor
  · rintro ⟨hz,hre⟩
    change (ModularGroup.T⁻¹•z).re=a at hre
    have hzr : z.re=a+1:=by linarith [hc.1]
    refine ⟨⟨by linarith,hzr.le,?_,?_⟩,hzr⟩
    · rw [hc.2,hre]
      linarith [hz.2.2.1]
    · rw [←hN]
      exact hz.2.2.1
  · rintro ⟨hz,hre⟩
    change z.re=a+1 at hre
    have hzr : (ModularGroup.T⁻¹•z).re=a:=by linarith [hc.1]
    refine ⟨⟨hzr.ge,by linarith,?_,?_⟩,hzr⟩
    · rw [hN]
      exact hz.2.2.2
    · rw [modular_normSq_sub_one,hzr,hN]
      linarith [hz.2.2.2]

theorem modular_shifted_vertical_side_pairing (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (fun z : ℍ=>ModularGroup.T•z) '' modularShiftedLeftSide a=modularShiftedRightSide a := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (modular_T_inv_shifted_rightSide a ha₁ ha₂ _).mp (by rw [inv_smul_smul];exact hw)
  · intro hz
    exact ⟨ModularGroup.T⁻¹•z,(modular_T_inv_shifted_rightSide a ha₁ ha₂ z).mpr hz,smul_inv_smul _ _⟩

theorem modular_S_unit_coordinates (z : ℍ) (hz : Complex.normSq (z:ℂ)=1) :
    Complex.normSq ((ModularGroup.S•z:ℍ):ℂ)=1 ∧ (ModularGroup.S•z).re= -z.re := by
  constructor
  · rw [modular_S_unit_circle z hz,Complex.normSq_neg,Complex.normSq_conj,hz]
  · change (((ModularGroup.S•z:ℍ):ℂ)).re= -z.re
    rw [modular_S_unit_circle z hz,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re]

theorem modular_S_shifted_selfArc (a : ℝ) (z : ℍ) (hz : z∈modularShiftedSelfArc a) :
    ModularGroup.S•z∈modularShiftedSelfArc a := by
  have hc:=modular_S_unit_coordinates z hz.1
  refine ⟨hc.1,?_,?_⟩ <;> rw [hc.2] <;> linarith [hz.2.1,hz.2.2]

theorem modular_shifted_self_arc_pairing (a : ℝ) :
    (fun z : ℍ=>ModularGroup.S•z) '' modularShiftedSelfArc a=modularShiftedSelfArc a := by
  ext z
  exact ⟨fun ⟨w,hw,he⟩=>he ▸ modular_S_shifted_selfArc a w hw,
    fun hz=>⟨ModularGroup.S•z,modular_S_shifted_selfArc a z hz,modular_S_involutive z⟩⟩

theorem modular_shifted_split_self_arc_pairing (a : ℝ) :
    (fun z : ℍ=>ModularGroup.S•z) '' modularShiftedSelfArcLeft a=modularShiftedSelfArcRight a := by
  ext z
  constructor
  · rintro ⟨w,⟨hw,hr⟩,rfl⟩
    refine ⟨modular_S_shifted_selfArc a w hw,?_⟩
    change 0≤(ModularGroup.S•w).re
    rw [(modular_S_unit_coordinates w hw.1).2]
    exact neg_nonneg.mpr hr
  · rintro ⟨hz,hr⟩
    refine ⟨ModularGroup.S•z,⟨modular_S_shifted_selfArc a z hz,?_⟩,modular_S_involutive z⟩
    change (ModularGroup.S•z).re≤0
    rw [(modular_S_unit_coordinates z hz.1).2]
    exact neg_nonpos.mpr hr

theorem modular_TS_shifted_pairedArc (a : ℝ) (z : ℍ) (hz : z∈modularShiftedPairedArc a) :
    (ModularGroup.T*ModularGroup.S)•z∈modularShiftedRightArc a := by
  have hS:=modular_S_unit_coordinates z hz.1
  have hT:=modular_T_coordinates (ModularGroup.S•z)
  rw [mul_smul]
  refine ⟨?_,?_,?_⟩
  · rw [modular_normSq_sub_one,hT.2,hT.1]
    linarith [hS.1]
  · rw [hT.1,hS.2]
    linarith [hz.2.2]
  · rw [hT.1,hS.2]
    linarith [hz.2.1]

theorem modular_shifted_arc_pairing (a : ℝ) :
    (fun z : ℍ=>(ModularGroup.T*ModularGroup.S)•z) '' modularShiftedPairedArc a=
      modularShiftedRightArc a := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact modular_TS_shifted_pairedArc a w hw
  · intro hz
    have hN : Complex.normSq ((ModularGroup.T⁻¹•z:ℍ):ℂ)=1:=by
      rw [modular_T_inv_coe]
      exact hz.1
    have hS:=modular_S_unit_coordinates (ModularGroup.T⁻¹•z) hN
    refine ⟨ModularGroup.S•(ModularGroup.T⁻¹•z),?_,?_⟩
    · refine ⟨hS.1,?_,?_⟩ <;> rw [hS.2,ModularGroup.re_T_inv_smul]
      · linarith [hz.2.2]
      · linarith [hz.2.1]
    · change (ModularGroup.T*ModularGroup.S)•(ModularGroup.S•(ModularGroup.T⁻¹•z))=z
      rw [mul_smul,modular_S_involutive,smul_inv_smul]

theorem modular_shifted_vertical_witness (a : ℝ) (b : ℝ) (hb : b=a ∨ b=a+1) :
    ∃z : ℍ,z.re=b ∧ z∈modularClosedShiftedPolygon a ∧
      1<Complex.normSq (z:ℂ) ∧ 1<Complex.normSq ((z:ℂ)-1) := by
  let z : ℍ:=⟨⟨b,2⟩,by norm_num⟩
  have hn : 1<Complex.normSq (z:ℂ):=by
    change 1<b*b+2*2
    nlinarith [sq_nonneg b]
  have hn' : 1<Complex.normSq ((z:ℂ)-1):=by
    change 1<(b-1)*(b-1)+(2-0)*(2-0)
    nlinarith [sq_nonneg (b-1)]
  refine ⟨z,rfl,⟨?_,?_,hn.le,hn'.le⟩,hn,hn'⟩
  · change a≤b
    rcases hb with rfl|rfl <;> linarith
  · change b≤a+1
    rcases hb with rfl|rfl <;> linarith

theorem modular_shifted_five_sides_pairwise (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularShiftedLeftSide a≠modularShiftedRightSide a ∧
    modularShiftedLeftSide a≠modularShiftedSelfArc a ∧
    modularShiftedLeftSide a≠modularShiftedPairedArc a ∧
    modularShiftedLeftSide a≠modularShiftedRightArc a ∧
    modularShiftedRightSide a≠modularShiftedSelfArc a ∧
    modularShiftedRightSide a≠modularShiftedPairedArc a ∧
    modularShiftedRightSide a≠modularShiftedRightArc a ∧
    modularShiftedSelfArc a≠modularShiftedPairedArc a ∧
    modularShiftedSelfArc a≠modularShiftedRightArc a ∧
    modularShiftedPairedArc a≠modularShiftedRightArc a := by
  obtain ⟨l,hlr,hlc,hln,hln'⟩:=modular_shifted_vertical_witness a a (Or.inl rfl)
  obtain ⟨r,hrr,hrc,hrn,hrn'⟩:=modular_shifted_vertical_witness a (a+1) (Or.inr rfl)
  have hL : l∈modularShiftedLeftSide a:=⟨hlc,hlr⟩
  have hR : r∈modularShiftedRightSide a:=⟨hrc,hrr⟩
  have hI : UpperHalfPlane.I∈modularShiftedSelfArc a:=by
    refine ⟨by norm_num,?_,?_⟩ <;> norm_num <;> linarith
  have hW : modularCutPoint a ha₁ ha₂∈modularShiftedPairedArc a:=by
    have hw:=modularCutPoint_properties a ha₁ ha₂
    exact ⟨hw.2.1,hw.1.ge,by linarith [hw.1,hw.2.2.2]⟩
  have neq {A B : Set ℍ} {z : ℍ} (hA : z∈A) (hB : z∉B) : A≠B:=by
    intro he
    exact hB (he ▸ hA)
  refine ⟨neq hL ?_,neq hL ?_,neq hL ?_,neq hL ?_,neq hR ?_,neq hR ?_,neq hR ?_,
    neq hI ?_,neq hI ?_,neq hW ?_⟩
  · rintro ⟨_,he⟩
    change l.re=a+1 at he
    linarith
  · intro h
    exact (ne_of_gt hln) h.1
  · intro h
    exact (ne_of_gt hln) h.1
  · intro h
    exact (ne_of_gt hln') h.1
  · intro h
    exact (ne_of_gt hrn) h.1
  · intro h
    exact (ne_of_gt hrn) h.1
  · intro h
    exact (ne_of_gt hrn') h.1
  · intro h
    have hh:=h.2.1
    change -a≤(0:ℝ) at hh
    linarith
  · intro h
    have hh:=h.2.1
    change (1/2:ℝ)≤0 at hh
    linarith
  · intro h
    have hh:=h.2.1
    rw [(modularCutPoint_properties a ha₁ ha₂).1] at hh
    linarith

def modularShiftedFiveSides (a : ℝ) : Set (Set ℍ):=
  {modularShiftedLeftSide a,modularShiftedRightSide a,modularShiftedSelfArc a,
    modularShiftedPairedArc a,modularShiftedRightArc a}

theorem modular_shifted_five_sides_card (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (modularShiftedFiveSides a).ncard=5 := by
  classical
  obtain ⟨hLR,hLS,hLP,hLA,hRS,hRP,hRA,hSP,hSA,hPA⟩:=modular_shifted_five_sides_pairwise a ha₁ ha₂
  have hL : modularShiftedLeftSide a∉({modularShiftedRightSide a,modularShiftedSelfArc a,
      modularShiftedPairedArc a,modularShiftedRightArc a}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hLR,hLS,hLP,hLA⟩
  have hR : modularShiftedRightSide a∉({modularShiftedSelfArc a,modularShiftedPairedArc a,
      modularShiftedRightArc a}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hRS,hRP,hRA⟩
  have hS : modularShiftedSelfArc a∉({modularShiftedPairedArc a,modularShiftedRightArc a}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hSP,hSA⟩
  rw [modularShiftedFiveSides,Set.ncard_insert_of_notMem hL,Set.ncard_insert_of_notMem hR,
    Set.ncard_insert_of_notMem hS,Set.ncard_pair hPA]

def modularShiftedSixSides (a : ℝ) : Set (Set ℍ):=
  {modularShiftedLeftSide a,modularShiftedRightSide a,modularShiftedSelfArcLeft a,
    modularShiftedSelfArcRight a,modularShiftedPairedArc a,modularShiftedRightArc a}

theorem modular_shifted_six_sides_card (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (modularShiftedSixSides a).ncard=6 := by
  classical
  let L:=modularShiftedLeftSide a
  let R:=modularShiftedRightSide a
  let A:=modularShiftedSelfArcLeft a
  let B:=modularShiftedSelfArcRight a
  let P:=modularShiftedPairedArc a
  let C:=modularShiftedRightArc a
  obtain ⟨hLR,_,hLP,hLC,_,hRP,hRC,_,_,hPC⟩:=modular_shifted_five_sides_pairwise a ha₁ ha₂
  obtain ⟨l,hlr,hlc,hln,_⟩:=modular_shifted_vertical_witness a a (Or.inl rfl)
  obtain ⟨r,hrr,hrc,hrn,_⟩:=modular_shifted_vertical_witness a (a+1) (Or.inr rfl)
  have hLl : l∈L:=⟨hlc,hlr⟩
  have hRr : r∈R:=⟨hrc,hrr⟩
  have hLA : L≠A:=by
    intro he
    have hh : l∈A:=he ▸ hLl
    exact (ne_of_gt hln) hh.1.1
  have hLB : L≠B:=by
    intro he
    have hh : l∈B:=he ▸ hLl
    exact (ne_of_gt hln) hh.1.1
  have hRA : R≠A:=by
    intro he
    have hh : r∈A:=he ▸ hRr
    exact (ne_of_gt hrn) hh.1.1
  have hRB : R≠B:=by
    intro he
    have hh : r∈B:=he ▸ hRr
    exact (ne_of_gt hrn) hh.1.1
  have hIS : UpperHalfPlane.I∈modularShiftedSelfArc a:=by
    refine ⟨by norm_num,?_,?_⟩ <;> norm_num <;> linarith
  have hIA : UpperHalfPlane.I∈A:=⟨hIS,by norm_num⟩
  have hIB : UpperHalfPlane.I∈B:=⟨hIS,by norm_num⟩
  have hIP : UpperHalfPlane.I∉P:=by
    intro h
    have hh:=h.2.1
    change -a≤(0:ℝ) at hh
    linarith
  have hIC : UpperHalfPlane.I∉C:=by
    intro h
    have hh:=h.2.1
    change (1/2:ℝ)≤0 at hh
    linarith
  have hAP : A≠P:=fun he=>hIP (he ▸ hIA)
  have hAC : A≠C:=fun he=>hIC (he ▸ hIA)
  have hBP : B≠P:=fun he=>hIP (he ▸ hIB)
  have hBC : B≠C:=fun he=>hIC (he ▸ hIB)
  have hAB : A≠B:=by
    let w:=modularCutPoint a ha₁ ha₂
    have hp:=modularCutPoint_properties a ha₁ ha₂
    have hw : w∈modularShiftedSelfArc a:=⟨hp.2.1,by linarith [hp.1],hp.1.le⟩
    have hS:=modular_S_unit_coordinates w hp.2.1
    have hSr : (ModularGroup.S•w).re=a:=by rw [hS.2,hp.1];ring
    have hSA : ModularGroup.S•w∈A:=⟨modular_S_shifted_selfArc a w hw,by change (ModularGroup.S•w).re≤0;rw [hSr];exact ha₂.le⟩
    intro he
    have hSB : ModularGroup.S•w∈B:=he ▸ hSA
    have hh:=hSB.2
    change 0≤(ModularGroup.S•w).re at hh
    rw [hSr] at hh
    linarith
  have hL : L∉({R,A,B,P,C}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hLR,hLA,hLB,hLP,hLC⟩
  have hR : R∉({A,B,P,C}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hRA,hRB,hRP,hRC⟩
  have hA : A∉({B,P,C}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hAB,hAP,hAC⟩
  have hB : B∉({P,C}:Set (Set ℍ)):=by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hBP,hBC⟩
  change ({L,R,A,B,P,C}:Set (Set ℍ)).ncard=6
  rw [Set.ncard_insert_of_notMem hL,Set.ncard_insert_of_notMem hR,
    Set.ncard_insert_of_notMem hA,Set.ncard_insert_of_notMem hB,Set.ncard_pair hPC]

theorem modular_S_normSq_mul (z : ℍ) :
    Complex.normSq ((ModularGroup.S•z:ℍ):ℂ)*Complex.normSq (z:ℂ)=1 := by
  rw [UpperHalfPlane.modular_S_smul]
  change Complex.normSq ((-(z:ℂ))⁻¹)*Complex.normSq (z:ℂ)=1
  rw [Complex.normSq_inv,Complex.normSq_neg,inv_mul_cancel₀ (Complex.normSq_pos.mpr z.ne_zero).ne']

theorem modular_TS_normSq_sub_one (z : ℍ) :
    Complex.normSq ((((ModularGroup.T*ModularGroup.S)•z:ℍ):ℂ)-1)=
      Complex.normSq ((ModularGroup.S•z:ℍ):ℂ) := by
  rw [mul_smul,modular_normSq_sub_one,(modular_T_coordinates _).2,(modular_T_coordinates _).1]
  ring

theorem modular_shifted_self_arc_tile_intersection (a : ℝ) (ha₁ : -(1/2)<a) (_ha₂ : a<0) :
    modularClosedShiftedPolygon a∩(fun z : ℍ=>ModularGroup.S•z) ⁻¹' modularClosedShiftedPolygon a=
      modularShiftedSelfArc a := by
  ext z
  constructor
  · rintro ⟨hz,hSz⟩
    have hN : Complex.normSq (z:ℂ)=1:=by
      have hm:=mul_le_mul_of_nonneg_right hSz.2.2.1 (Complex.normSq_nonneg (z:ℂ))
      rw [one_mul,modular_S_normSq_mul] at hm
      exact le_antisymm hm hz.2.2.1
    refine ⟨hN,hz.1,?_⟩
    have hr:=hSz.1
    rw [(modular_S_unit_coordinates z hN).2] at hr
    linarith
  · intro hz
    have hzL : z∈modularShiftedLeftArc a:=⟨hz.1,hz.2.1,by linarith [hz.2.2]⟩
    have hSL : ModularGroup.S•z∈modularShiftedLeftArc a:=by
      have hS:=modular_S_shifted_selfArc a z hz
      exact ⟨hS.1,hS.2.1,by linarith [hS.2.2]⟩
    exact ⟨modular_shifted_left_arc_closed a ha₁ z hzL,
      modular_shifted_left_arc_closed a ha₁ _ hSL⟩

theorem modular_shifted_paired_arc_tile_intersection (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularClosedShiftedPolygon a∩(fun z : ℍ=>(ModularGroup.T*ModularGroup.S)•z) ⁻¹'
      modularClosedShiftedPolygon a=modularShiftedPairedArc a := by
  ext z
  constructor
  · rintro ⟨hz,hTSz⟩
    have hSN : 1≤Complex.normSq ((ModularGroup.S•z:ℍ):ℂ):=by
      have hh:=hTSz.2.2.2
      rw [modular_TS_normSq_sub_one] at hh
      exact hh
    have hN : Complex.normSq (z:ℂ)=1:=by
      have hm:=mul_le_mul_of_nonneg_right hSN (Complex.normSq_nonneg (z:ℂ))
      rw [one_mul,modular_S_normSq_mul] at hm
      exact le_antisymm hm hz.2.2.1
    have hSr:=(modular_S_unit_coordinates z hN).2
    have hTr : ((ModularGroup.T*ModularGroup.S)•z).re=1-z.re:=by
      rw [mul_smul,(modular_T_coordinates _).1,hSr]
      ring
    refine ⟨hN,?_,?_⟩
    · have hh:=hTSz.2.1
      rw [hTr] at hh
      linarith
    · have hh:=hz.2.2.2
      rw [modular_normSq_sub_one,hN] at hh
      linarith
  · intro hz
    have hzL : z∈modularShiftedLeftArc a:=⟨hz.1,by linarith [hz.2.1],hz.2.2⟩
    exact ⟨modular_shifted_left_arc_closed a ha₁ z hzL,
      modular_shifted_right_arc_closed a ha₂ _ (modular_TS_shifted_pairedArc a z hz)⟩

theorem modular_shifted_left_side_tile_intersection (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularClosedShiftedPolygon a∩(fun z : ℍ=>ModularGroup.T•z) ⁻¹' modularClosedShiftedPolygon a=
      modularShiftedLeftSide a := by
  ext z
  constructor
  · rintro ⟨hz,hTz⟩
    refine ⟨hz,?_⟩
    change z.re=a
    have hh:=hTz.2.1
    rw [(modular_T_coordinates z).1] at hh
    linarith [hz.1]
  · intro hz
    have hR : ModularGroup.T•z∈modularShiftedRightSide a:=
      (modular_T_inv_shifted_rightSide a ha₁ ha₂ _).mp (by rw [inv_smul_smul];exact hz)
    exact ⟨hz.1,hR.1⟩

end LowDimensionalTopology.Geometry.Fuchsian
