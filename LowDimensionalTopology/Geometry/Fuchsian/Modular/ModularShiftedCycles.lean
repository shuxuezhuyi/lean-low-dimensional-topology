/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedFundamental
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Topology ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The literal orbit cycle in the actual native modular action and actual polygon closure. -/
def modularNativePolygonCycle (D : Set ℍ) (z : ℍ) : Set ℍ:=
  closure D∩MulAction.orbit modularNativeHom.range z

theorem modularNativePolygonCycle_mem (D : Set ℍ) (z w : ℍ) :
    w∈modularNativePolygonCycle D z ↔ w∈closure D ∧
      ∃A : Matrix.SpecialLinearGroup (Fin 2) ℤ,A•z=w := by
  constructor
  · rintro ⟨hw,⟨g,hg⟩⟩
    obtain ⟨A,hA⟩:=g.property
    refine ⟨hw,A,?_⟩
    rw [←modularNativeHom_apply A z,hA]
    exact hg
  · rintro ⟨hw,A,hA⟩
    refine ⟨hw,⟨⟨modularNativeHom A,⟨A,rfl⟩⟩,?_⟩⟩
    change modularNativeHom A z=w
    rw [modularNativeHom_apply]
    exact hA

theorem modular_fd_positive_strip_representatives (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ)
    (hz : z∈ModularGroup.fd) (hAz : A•z∈ModularGroup.fd) (hl : 0<z.re) (hr : z.re<1/2) :
    A•z=z ∨ A•z=ModularGroup.S•z := by
  have hnrho : z≠UpperHalfPlane.ρ:=by
    intro he
    rw [he] at hl
    norm_num [UpperHalfPlane.ρ] at hl
  have hnrho' : z≠(1:ℝ)+ᵥUpperHalfPlane.ρ:=by
    intro he
    rw [he] at hr
    norm_num [UpperHalfPlane.ρ] at hr
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz hAz with
    h|⟨_,hx⟩|⟨_,hx⟩|⟨h,_⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩
  · left
    rcases h with rfl|rfl
    · exact one_smul _ _
    · rw [ModularGroup.SL_neg_smul,one_smul]
  · exact False.elim (by linarith)
  · exact False.elim (by linarith)
  · right
    rcases h with rfl|rfl
    · rfl
    · rw [ModularGroup.SL_neg_smul]
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)

theorem modular_T_inv_coe (z : ℍ) :
    ((ModularGroup.T⁻¹•z:ℍ):ℂ)=(z:ℂ)-1 := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [ModularGroup.T,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  ring

theorem modularShiftReduced_closed_fd (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℍ) (hz : z∈modularClosedShiftedPolygon a) : modularShiftReduced z∈ModularGroup.fd := by
  by_cases hl : z.re≤1/2
  · simp only [modularShiftReduced,modularShiftFold,ite_eq_left hl,one_smul]
    exact ⟨hz.2.2.1,abs_le.mpr ⟨by linarith [hz.1],hl⟩⟩
  · simp only [modularShiftReduced,modularShiftFold,ite_eq_right hl]
    refine ⟨?_,?_⟩
    · rw [modular_T_inv_coe]
      exact hz.2.2.2
    · rw [ModularGroup.re_T_inv_smul]
      exact abs_le.mpr ⟨by linarith,by linarith [hz.2.1]⟩

def modularCutPoint (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) : ℍ:=
  modularRoundPoint (-a) (by rw [abs_neg,abs_of_neg ha₂];linarith)

theorem modularCutPoint_properties (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (modularCutPoint a ha₁ ha₂).re= -a ∧
      Complex.normSq (modularCutPoint a ha₁ ha₂:ℂ)=1 ∧
      0<(modularCutPoint a ha₁ ha₂).re ∧ (modularCutPoint a ha₁ ha₂).re<1/2 := by
  refine ⟨rfl,modularRoundPoint_norm _ _,?_,?_⟩ <;> dsimp [modularCutPoint,modularRoundPoint] <;> linarith

theorem modular_cut_cycle_points_closed (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    let w:=modularCutPoint a ha₁ ha₂
    w∈modularClosedShiftedPolygon a ∧ ModularGroup.S•w∈modularClosedShiftedPolygon a ∧
      (ModularGroup.T*ModularGroup.S)•w∈modularClosedShiftedPolygon a := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hSN : Complex.normSq ((ModularGroup.S•w:ℍ):ℂ)=1:=by
    rw [modular_S_unit_circle w hp.2.1,Complex.normSq_neg,Complex.normSq_conj]
    exact hp.2.1
  have hSr : (ModularGroup.S•w).re=a:=by
    change (((ModularGroup.S•w:ℍ):ℂ)).re=a
    rw [modular_S_unit_circle w hp.2.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re,hp.1]
    ring
  have hTc:=modular_T_coordinates (ModularGroup.S•w)
  change w∈modularClosedShiftedPolygon a ∧ ModularGroup.S•w∈modularClosedShiftedPolygon a ∧
    (ModularGroup.T*ModularGroup.S)•w∈modularClosedShiftedPolygon a
  refine ⟨⟨?_,?_,hp.2.1.ge,?_⟩,⟨?_,?_,hSN.ge,?_⟩,?_⟩
  · rw [hp.1]
    linarith
  · rw [hp.1]
    linarith
  · rw [modular_normSq_sub_one,hp.2.1,hp.1]
    linarith
  · rw [hSr]
  · rw [hSr]
    linarith
  · rw [modular_normSq_sub_one,hSN,hSr]
    linarith
  · rw [mul_smul]
    refine ⟨?_,?_,?_,?_⟩
    · rw [hTc.1,hSr]
      linarith
    · rw [hTc.1,hSr]
    · rw [hTc.2,hSN,hSr]
      linarith
    · rw [modular_normSq_sub_one,hTc.2,hTc.1,hSN,hSr]
      linarith


theorem modular_cut_cycle (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    let w:=modularCutPoint a ha₁ ha₂
    modularNativePolygonCycle (modularShiftedPolygon a) w=
      {w,ModularGroup.S•w,(ModularGroup.T*ModularGroup.S)•w} := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hclosed:=modular_cut_cycle_points_closed a ha₁ ha₂
  have hwfd : w∈ModularGroup.fd:=⟨hp.2.1.ge,abs_le.mpr ⟨by linarith [hp.2.2.1],hp.2.2.2.le⟩⟩
  change modularNativePolygonCycle (modularShiftedPolygon a) w={w,ModularGroup.S•w,(ModularGroup.T*ModularGroup.S)•w}
  ext y
  rw [modularNativePolygonCycle_mem,modularShiftedPolygon_closure]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy,A,hA⟩
    let B:=modularShiftFold y
    have hred:=modularShiftReduced_closed_fd a ha₁ ha₂ y hy
    have hact : (B*A)•w=modularShiftReduced y:=by
      change (B*A)•w=B•y
      rw [mul_smul,hA]
    have hrep:=modular_fd_positive_strip_representatives (B*A) w hwfd
      (hact.symm ▸ hred) hp.2.2.1 hp.2.2.2
    rw [hact] at hrep
    by_cases hcut : y.re≤1/2
    · simp only [modularShiftReduced,modularShiftFold,ite_eq_left hcut,one_smul] at hrep
      rcases hrep with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hyrec : y=ModularGroup.T•modularShiftReduced y:=by
        change y=ModularGroup.T•((if y.re≤1/2 then 1 else ModularGroup.T⁻¹)•y)
        rw [ite_eq_right hcut,smul_inv_smul]
      rcases hrep with h|h
      · have hTy : y.re=w.re+1:=by
          rw [hyrec,h]
          exact (modular_T_coordinates w).1
        have hbound:=hy.2.1
        have hwr : w.re= -a:=hp.1
        exact False.elim (by linarith)
      · right;right
        rw [hyrec,h,mul_smul]
  · rintro (rfl|rfl|rfl)
    · exact ⟨hclosed.1,1,one_smul _ _⟩
    · exact ⟨hclosed.2.1,ModularGroup.S,rfl⟩
    · exact ⟨hclosed.2.2,ModularGroup.T*ModularGroup.S,rfl⟩


theorem modular_fd_positive_strip_matrices (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ)
    (hz : z∈ModularGroup.fd) (hAz : A•z∈ModularGroup.fd) (hl : 0<z.re) (hr : z.re<1/2) :
    A=1 ∨ A=-1 ∨ A=ModularGroup.S ∨ A=-ModularGroup.S := by
  have hnrho : z≠UpperHalfPlane.ρ:=by intro he;rw [he] at hl;norm_num [UpperHalfPlane.ρ] at hl
  have hnrho' : z≠(1:ℝ)+ᵥUpperHalfPlane.ρ:=by intro he;rw [he] at hr;norm_num [UpperHalfPlane.ρ] at hr
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz hAz with
    h|⟨_,hx⟩|⟨_,hx⟩|⟨h,_⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩
  · exact h.elim Or.inl (fun h=>Or.inr (Or.inl h))
  · exact False.elim (by linarith)
  · exact False.elim (by linarith)
  · exact Or.inr (Or.inr h)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho' he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)
  · exact False.elim (hnrho he)

theorem modularCutPoint_stabilizer_trivial (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (g : modularNativeHom.range) (hg : g.val (modularCutPoint a ha₁ ha₂)=modularCutPoint a ha₁ ha₂) : g=1 := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hw : w∈ModularGroup.fd:=⟨hp.2.1.ge,abs_le.mpr ⟨by linarith [hp.2.2.1],hp.2.2.2.le⟩⟩
  obtain ⟨A,hA⟩:=g.property
  have hAw : A•w=w:=by rw [←modularNativeHom_apply A w,hA];exact hg
  have hm:=modular_fd_positive_strip_matrices A w hw (hAw.symm ▸ hw) hp.2.2.1 hp.2.2.2
  have hS : ModularGroup.S•w≠w:=by
    intro he
    have hc:=congrArg (fun z : ℍ=>(z:ℂ)) he
    rw [modular_S_unit_circle w hp.2.1] at hc
    have hr:=congrArg Complex.re hc
    simp only [Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re] at hr
    linarith [hp.2.2.1]
  rcases hm with h|h|h|h
  · apply Subtype.ext
    rw [←hA,h,map_one]
    rfl
  · apply Subtype.ext
    rw [←hA,h,modularNativeHom_neg_one]
    rfl
  · exact False.elim (hS (h ▸ hAw))
  · rw [h,ModularGroup.SL_neg_smul] at hAw
    exact False.elim (hS hAw)

theorem modular_cut_cycle_card (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    (modularNativePolygonCycle (modularShiftedPolygon a) (modularCutPoint a ha₁ ha₂)).ncard=3 := by
  classical
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hSr : (ModularGroup.S•w).re=a:=by
    change (((ModularGroup.S•w:ℍ):ℂ)).re=a
    rw [modular_S_unit_circle w hp.2.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re,hp.1]
    ring
  have hTr : ((ModularGroup.T*ModularGroup.S)•w).re=a+1:=by rw [mul_smul,(modular_T_coordinates _).1,hSr]
  have hWS : w≠ModularGroup.S•w:=by intro he;have hh:=congrArg UpperHalfPlane.re he;rw [hp.1,hSr] at hh;linarith
  have hWT : w≠(ModularGroup.T*ModularGroup.S)•w:=by intro he;have hh:=congrArg UpperHalfPlane.re he;rw [hp.1,hTr] at hh;linarith
  have hST : ModularGroup.S•w≠(ModularGroup.T*ModularGroup.S)•w:=by intro he;have hh:=congrArg UpperHalfPlane.re he;rw [hSr,hTr] at hh;linarith
  rw [modular_cut_cycle]
  change ({w,ModularGroup.S•w,(ModularGroup.T*ModularGroup.S)•w}:Set ℍ).ncard=3
  have hwNot : w ∉ ({ModularGroup.S•w,(ModularGroup.T*ModularGroup.S)•w}:Set ℍ) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨hWS,hWT⟩
  rw [Set.ncard_insert_of_notMem hwNot,Set.ncard_pair hST]

theorem modularShiftReduced_re_lower (a : ℝ) (ha₁ : -(1/2)<a) (_ha₂ : a<0)
    (z : ℍ) (hz : z∈modularClosedShiftedPolygon a) : -(1/2)<(modularShiftReduced z).re := by
  by_cases hl : z.re≤1/2
  · simp only [modularShiftReduced,modularShiftFold,ite_eq_left hl,one_smul]
    linarith [hz.1]
  · simp only [modularShiftReduced,modularShiftFold,ite_eq_right hl,ModularGroup.re_T_inv_smul]
    linarith

theorem modular_fd_I_representative (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hAz : A•UpperHalfPlane.I∈ModularGroup.fd) : A•UpperHalfPlane.I=UpperHalfPlane.I := by
  have hnρ : UpperHalfPlane.I≠UpperHalfPlane.ρ:=by
    intro h;have hh:=congrArg UpperHalfPlane.re h;norm_num [UpperHalfPlane.ρ] at hh
  have hnρ' : UpperHalfPlane.I≠(1:ℝ)+ᵥUpperHalfPlane.ρ:=by
    intro h;have hh:=congrArg UpperHalfPlane.re h;norm_num [UpperHalfPlane.ρ] at hh
  have hS : ModularGroup.S•UpperHalfPlane.I=UpperHalfPlane.I:=by
    rw [←modularNativeHom_apply]
    exact modular_I_fixed_order_two.1
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd ModularGroup.I_mem_fd hAz with
    h|⟨_,hx⟩|⟨_,hx⟩|⟨h,_⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩
  · rcases h with rfl|rfl
    · exact one_smul _ _
    · rw [ModularGroup.SL_neg_smul,one_smul]
  · norm_num at hx
  · norm_num at hx
  · rcases h with rfl|rfl
    · exact hS
    · rw [ModularGroup.SL_neg_smul,hS]
  · exact False.elim (hnρ' he)
  · exact False.elim (hnρ' he)
  · exact False.elim (hnρ' he)
  · exact False.elim (hnρ he)
  · exact False.elim (hnρ he)
  · exact False.elim (hnρ he)

theorem modular_I_closed_shifted (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    UpperHalfPlane.I∈modularClosedShiftedPolygon a := by
  refine ⟨by norm_num;linarith,by norm_num;linarith,?_,?_⟩
  · norm_num
  · rw [modular_normSq_sub_one]
    norm_num

theorem modular_shifted_I_cycle (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularNativePolygonCycle (modularShiftedPolygon a) UpperHalfPlane.I={UpperHalfPlane.I} := by
  ext y
  rw [modularNativePolygonCycle_mem,modularShiftedPolygon_closure a]
  constructor
  · rintro ⟨hy,A,hA⟩
    let B:=modularShiftFold y
    have hred:=modularShiftReduced_closed_fd a ha₁ ha₂ y hy
    have hact : (B*A)•UpperHalfPlane.I=modularShiftReduced y:=by
      change (B*A)•UpperHalfPlane.I=B•y
      rw [mul_smul,hA]
    have hrep:=modular_fd_I_representative (B*A) (hact.symm ▸ hred)
    rw [hact] at hrep
    by_cases hcut : y.re≤1/2
    · simpa only [modularShiftReduced,modularShiftFold,ite_eq_left hcut,one_smul,
        Set.mem_singleton_iff] using hrep
    · have hyrec : y=ModularGroup.T•modularShiftReduced y:=by
        change y=ModularGroup.T•((if y.re≤1/2 then 1 else ModularGroup.T⁻¹)•y)
        rw [ite_eq_right hcut,smul_inv_smul]
      have hyr : y.re=1:=by rw [hyrec,hrep,(modular_T_coordinates _).1];norm_num
      exact False.elim (by linarith [hy.2.1])
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨modular_I_closed_shifted a ha₁ ha₂,1,one_smul _ _⟩

def modularZeta : ℍ:=modularRoundPoint (1/2) (by norm_num)

theorem modularZeta_properties :
    modularZeta.re=1/2 ∧ Complex.normSq (modularZeta:ℂ)=1 ∧ modularZeta∈ModularGroup.fd := by
  have hn : Complex.normSq (modularZeta:ℂ)=1:=modularRoundPoint_norm (1/2) (by norm_num)
  exact ⟨rfl,hn,hn.ge,by change |(1/2:ℝ)|≤1/2;norm_num⟩

theorem modular_fd_zeta_right_representative (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hAz : A•modularZeta∈ModularGroup.fd) (hl : -(1/2)<(A•modularZeta).re) :
    A•modularZeta=modularZeta := by
  let t:=A•modularZeta
  have hSi : ∀u : ℍ,Complex.normSq (u:ℂ)=1→(ModularGroup.S•u).im=u.im:=by
    intro u hu
    have hh:=congrArg Complex.im (modular_S_unit_circle u hu)
    simpa only [UpperHalfPlane.coe_im,Complex.neg_im,Complex.conj_im,neg_neg] using hh
  have hTiN : Complex.normSq ((ModularGroup.T⁻¹•modularZeta:ℍ):ℂ)=1:=by
    rw [modular_T_inv_coe,modular_normSq_sub_one,modularZeta_properties.2.1,modularZeta_properties.1]
    norm_num
  have hnρ : modularZeta≠UpperHalfPlane.ρ:=by
    intro h
    have hh:=congrArg UpperHalfPlane.re h
    rw [modularZeta_properties.1] at hh
    norm_num [UpperHalfPlane.ρ] at hh
  have him : t.im=modularZeta.im:=by
    change (A•modularZeta).im=modularZeta.im
    rcases ModularGroup.cases_of_mem_fd_smul_mem_fd modularZeta_properties.2.2 hAz with
      h|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨_,he⟩|⟨_,he⟩|⟨_,he⟩
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,one_smul]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,ModularGroup.im_T_smul]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,ModularGroup.im_T_inv_smul]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,hSi _ modularZeta_properties.2.1]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,mul_smul,
        ModularGroup.im_T_smul,hSi _ modularZeta_properties.2.1]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,mul_smul,
        ModularGroup.im_T_inv_smul,hSi _ hTiN]
    · rcases h with rfl|rfl <;> simp only [ModularGroup.SL_neg_smul,mul_smul,
        hSi _ hTiN,ModularGroup.im_T_inv_smul]
    · exact False.elim (hnρ he)
    · exact False.elim (hnρ he)
    · exact False.elim (hnρ he)
  have hzsq : modularZeta.im*modularZeta.im=3/4:=by
    have hn:=modularZeta_properties.2.1
    rw [Complex.normSq_apply] at hn
    change modularZeta.re*modularZeta.re+modularZeta.im*modularZeta.im=1 at hn
    rw [modularZeta_properties.1] at hn
    nlinarith
  have hn : 1≤t.re*t.re+t.im*t.im:=hAz.1
  rw [him,hzsq] at hn
  have hu : t.re≤1/2:=(abs_le.mp hAz.2).2
  have hre : t.re=1/2:=by
    by_contra hne
    have hp : (t.re+1/2)*(t.re-1/2)<0:=
      mul_neg_of_pos_of_neg (by linarith) (by exact sub_neg.mpr (lt_of_le_of_ne hu hne))
    nlinarith
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change t.re=modularZeta.re
    rw [hre,modularZeta_properties.1]
  · exact him

theorem modular_zeta_closed_shifted (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularZeta∈modularClosedShiftedPolygon a := by
  have hp:=modularZeta_properties
  refine ⟨?_,?_,hp.2.1.ge,?_⟩
  · rw [hp.1];linarith
  · rw [hp.1];linarith
  · rw [modular_normSq_sub_one,hp.2.1,hp.1]
    norm_num

theorem modular_shifted_zeta_cycle (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularNativePolygonCycle (modularShiftedPolygon a) modularZeta={modularZeta} := by
  ext y
  rw [modularNativePolygonCycle_mem,modularShiftedPolygon_closure a]
  constructor
  · rintro ⟨hy,A,hA⟩
    let B:=modularShiftFold y
    have hred:=modularShiftReduced_closed_fd a ha₁ ha₂ y hy
    have hlow:=modularShiftReduced_re_lower a ha₁ ha₂ y hy
    have hact : (B*A)•modularZeta=modularShiftReduced y:=by
      change (B*A)•modularZeta=B•y
      rw [mul_smul,hA]
    have hrep:=modular_fd_zeta_right_representative (B*A) (hact.symm ▸ hred) (hact.symm ▸ hlow)
    rw [hact] at hrep
    by_cases hcut : y.re≤1/2
    · simpa only [modularShiftReduced,modularShiftFold,ite_eq_left hcut,one_smul,
        Set.mem_singleton_iff] using hrep
    · have hyrec : y=ModularGroup.T•modularShiftReduced y:=by
        change y=ModularGroup.T•((if y.re≤1/2 then 1 else ModularGroup.T⁻¹)•y)
        rw [ite_eq_right hcut,smul_inv_smul]
      have hyr : y.re=3/2:=by rw [hyrec,hrep,(modular_T_coordinates _).1,modularZeta_properties.1];ring
      exact False.elim (by linarith [hy.2.1])
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨modular_zeta_closed_shifted a ha₁ ha₂,1,one_smul _ _⟩

end LowDimensionalTopology.Geometry.Fuchsian
