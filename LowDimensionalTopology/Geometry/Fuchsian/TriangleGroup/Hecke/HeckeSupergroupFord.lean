/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeSupergroupGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The normalized actual source inversion has zero lower-right coefficient. -/
theorem unitHeckeInversionSL_lowerRight (q : ℕ∞) (hq : 3≤q) :
    unitHeckeInversionSL q hq 1 1=0 := by
  simp [unitHeckeInversionSL,unitHeckeDilationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply,Matrix.adjugate_fin_two,Fin.sum_univ_two,
    modularInversionSL]

/-- The source corner has its actual positively rescaled unit-circle norm. -/
theorem unitHeckeCorner_norm (n : ℕ) (hn : 3≤n) :
    ‖(unitHeckeCorner n hn:ℂ)‖=1/(2*Real.cos (triangleOrderAngle n)) := by
  change ‖((unitHeckeDilationSL n (by exact_mod_cast hn)•standardHeckeCorner n hn:ℍ):ℂ)‖=_
  unfold unitHeckeDilationSL
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (hecke_width_pos n (by exact_mod_cast hn))),standardHeckeCorner_norm,mul_one]

/-- The actual Hecke inversion forces every common exterior point outside the true corner circle. -/
theorem finiteHecke_exterior_norm_ge_corner (n : ℕ) (hn : 3≤n)
    (z : ℍ) (hz : z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (unitHeckeMobiusGroup n (by exact_mod_cast hn))) :
    Complex.normSq (unitHeckeCorner n hn:ℂ)≤Complex.normSq (z:ℂ) := by
  have hc:=hecke_width_pos n (by exact_mod_cast hn)
  have hh:=hz ⟨unitHeckeInversionSL n (by exact_mod_cast hn),unitHeckeInversionSL_mem n (by exact_mod_cast hn)⟩
  change 1≤‖((unitHeckeInversionSL n (by exact_mod_cast hn) 1 0:ℝ):ℂ)*(z:ℂ)+
    ((unitHeckeInversionSL n (by exact_mod_cast hn) 1 1:ℝ):ℂ)‖ at hh
  rw [unitHeckeInversionSL_lowerLeft,unitHeckeInversionSL_lowerRight,Complex.ofReal_zero,add_zero,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc] at hh
  have hnorm : ‖(unitHeckeCorner n hn:ℂ)‖≤‖(z:ℂ)‖ := by
    rw [unitHeckeCorner_norm]
    exact (div_le_iff₀ hc).mpr (by nlinarith only [hh])
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  nlinarith only [hnorm,norm_nonneg (unitHeckeCorner n hn:ℂ),norm_nonneg (z:ℂ)]

/-- The true two sharp corners control the actual whole-supergroup exterior throughout the centered strip. -/
theorem finiteHecke_supergroup_centered_exterior (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G)
    (z : ℍ) (hx : |z.re|≤(1:ℝ)/2)
    (hz : z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (unitHeckeMobiusGroup n (by exact_mod_cast hn))) :
    z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior G := by
  have hw:=finiteHecke_supergroup_corner_exterior n hn G P hsub
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈G:=hsub (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn))
  have hw' :=parabolicFordExterior_integer_translate G hT (unitHeckeCorner n hn) hw (-1)
  intro A
  exact hecke_denominator_two_corners A.val _ (unitHeckeCorner_re n hn)
    (hw ⟨A.val,A.property⟩) (by simpa only [Int.cast_neg,Int.cast_one] using hw' ⟨A.val,A.property⟩)
    z hx (finiteHecke_exterior_norm_ge_corner n hn z hz)

/-- Integer translation followed by its opposite is the identity on actual half-plane points. -/
theorem hecke_integer_translate_cancel (k : ℤ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k:ℝ)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-k:ℝ)•z)=z := by
  apply UpperHalfPlane.ext
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  push_cast
  ring

/-- Every genuine finite-Hecke supergroup has precisely the same full common Ford exterior. -/
theorem finiteHecke_supergroup_fordExterior_eq (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior G=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (unitHeckeMobiusGroup n (by exact_mod_cast hn)) := by
  ext z
  constructor
  · intro hz A
    exact hz ⟨A.val,hsub A.property⟩
  · intro hz
    let k:ℤ:=round z.re
    let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-k:ℝ)•z
    have hT0:=unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)
    have hw : w∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (unitHeckeMobiusGroup n (by exact_mod_cast hn)) := by
      simpa only [Int.cast_neg,w] using parabolicFordExterior_integer_translate _ hT0 z hz (-k)
    have hx : |w.re|≤(1:ℝ)/2 := by
      have hre : w.re=z.re-(k:ℝ) := by
        change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-k:ℝ)•z:ℍ):ℂ).re=_
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
        simp only [Complex.add_re,UpperHalfPlane.coe_re,Complex.ofReal_re]
        ring
      rw [hre]
      exact abs_sub_round z.re
    have hwG:=finiteHecke_supergroup_centered_exterior n hn G P hsub w hx hw
    have hh:=parabolicFordExterior_integer_translate G (hsub hT0) w hwG k
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (k:ℝ)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-k:ℝ)•z)∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior G at hh
    rwa [hecke_integer_translate_cancel] at hh

/-- The literal closed Ford strips of an actual finite-Hecke supergroup coincide. -/
theorem finiteHecke_supergroup_closedFord_eq (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    parabolicFordClosedStrip G=parabolicFordClosedStrip (unitHeckeMobiusGroup n (by exact_mod_cast hn)) := by
  unfold parabolicFordClosedStrip
  rw [finiteHecke_supergroup_fordExterior_eq n hn G P hsub]

/-- The original native half-plane action is unchanged by actual subgroup inclusion. -/
theorem hecke_native_subgroup_action {H G : Subgroup Mobius.complexMobiusGroup}
    (Q : HalfPlaneFuchsianGroup H) (P : HalfPlaneFuchsianGroup G) (hsub : H≤G)
    (g : H) (z : ℍ) :
    letI:=Q.nativeAction
    letI:=P.nativeAction
    g•z=(⟨g.val,hsub g.property⟩:G)•z := by
  let :=Q.nativeAction
  let :=P.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←Q.nativeAction_boundary,←P.nativeAction_boundary]

/-- An actual discrete supergroup preserving the source half-plane equals the finite Hecke group. -/
theorem finiteHecke_halfPlane_supergroup_eq (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    G=unitHeckeMobiusGroup n (by exact_mod_cast hn) := by
  let H:=unitHeckeMobiusGroup n (by exact_mod_cast hn)
  let Q:=unitHeckeMobiusData n (by exact_mod_cast hn)
  let :=Q.nativeAction
  let :=P.nativeAction
  have hT0 : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H:=unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈G:=hsub hT0
  have hstab:=finiteHecke_supergroup_infty_stabilizer n hn G P hsub
  have heq:=finiteHecke_supergroup_closedFord_eq n hn G P hsub
  obtain ⟨z,hz⟩:=parabolicFordDomain_nonempty G P.discrete hT
  have hzstrict:=parabolicFordDomain_subset_strictStrip G hz
  apply le_antisymm _ hsub
  intro f hf
  let F:G:=⟨f,hf⟩
  obtain ⟨g,hg⟩:=parabolicFordClosedStrip_orbit_representative Q hT0 (F⁻¹•z)
  let a:G:=⟨g.val,hsub g.property⟩
  have hact : g•(F⁻¹•z)=a•(F⁻¹•z) := hecke_native_subgroup_action Q P hsub g _
  have hu : a•(F⁻¹•z)∈parabolicFordClosedStrip G := by
    rw [heq,←hact]
    exact hg
  let k:G:=F*a⁻¹
  have hzmem : z∈k•parabolicFordClosedStrip G := by
    refine ⟨a•(F⁻¹•z),hu,?_⟩
    change (F*a⁻¹)•(a•(F⁻¹•z))=z
    simp only [mul_smul,inv_smul_smul,smul_inv_smul]
  have hk : k=1:=parabolicFordStrictStrip_closed_tile_unique P hstab z hzstrict k hzmem
  have hFa : F=a := by
    have hh:=congrArg (fun b:G=>b*a) hk
    change (F*a⁻¹)*a=1*a at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh
  have he : f=g.val:=congrArg Subtype.val hFa
  exact he ▸ g.property

end LowDimensionalTopology.Geometry.Fuchsian
