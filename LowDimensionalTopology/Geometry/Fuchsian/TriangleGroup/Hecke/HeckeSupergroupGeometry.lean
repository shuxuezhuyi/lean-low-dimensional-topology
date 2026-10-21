/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.InfiniteUnitHeckeCuspStabilizer
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

/-- The finite Hecke inversion supplies an actual positive coefficient strictly below two. -/
theorem finite_unitHecke_lowerLeft_bounds (n : ℕ) (hn : 3≤n) :
    0<unitHeckeInversionSL n (by exact_mod_cast hn) 1 0 ∧
      |unitHeckeInversionSL n (by exact_mod_cast hn) 1 0| < 2 := by
  have hc : 0<unitHeckeInversionSL n (by exact_mod_cast hn) 1 0 := by
    rw [unitHeckeInversionSL_lowerLeft]
    exact hecke_width_pos n (by exact_mod_cast hn)
  refine ⟨hc,?_⟩
  have hangle:=hecke_order_angle_bounds n (by exact_mod_cast hn)
  have hpos : 0<triangleOrderAngle n := by
    rw [triangleOrderAngle_nat]
    exact div_pos Real.pi_pos (by exact_mod_cast (by omega : 0<n))
  have hcos : Real.cos (triangleOrderAngle n)<1 := by
    have hh:=Real.strictAntiOn_cos (show (0:ℝ)∈Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show triangleOrderAngle n∈Icc 0 Real.pi by constructor <;> linarith [hangle.1,hangle.2,Real.pi_pos]) hpos
    simpa only [Real.cos_zero] using hh
  rw [abs_of_pos hc,unitHeckeInversionSL_lowerLeft]
  linarith only [hcos]

/-- Every actual translation in any discrete finite-Hecke supergroup has an integral period. -/
theorem finiteHecke_supergroup_translation_integer (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G)
    (t : ℝ) (ht : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈G) : ∃k : ℤ,t=(k:ℝ) := by
  have hb:=finite_unitHecke_lowerLeft_bounds n hn
  exact primitive_translation_integer G hd
    (hsub (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)))
    (unitHeckeInversionSL n (by exact_mod_cast hn))
    (hsub (unitHeckeInversionSL_mem n (by exact_mod_cast hn))) hb.1.ne' hb.2 t ht

/-- The full infinity stabilizer of any actual invariant-half-plane finite-Hecke supergroup is unchanged. -/
theorem finiteHecke_supergroup_infty_stabilizer (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G ∞=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  have hb:=finite_unitHecke_lowerLeft_bounds n hn
  exact primitive_unit_stabilizer_of_lowerLeft G P
    (hsub (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)))
    (unitHeckeInversionSL n (by exact_mod_cast hn))
    (hsub (unitHeckeInversionSL_mem n (by exact_mod_cast hn))) hb.1.ne' hb.2

/-- Inclusion in a discrete actual supergroup preserves the exact full stabilizer order at the sharp Hecke corner. -/
theorem finiteHecke_supergroup_corner_order (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    fordPointOrder G (unitHeckeCorner n hn)=n := by
  let z:=unitHeckeCorner n hn
  have hp : ∀f∈G,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=fun f hf=>P.preserves ⟨f,hf⟩
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈G:=hsub (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn))
  have hl : n≤fordPointOrder G z:=by
    have h:=elliptic_order_le_fordPointOrder G P.discrete hp _
      (hsub (unitHeckeMobiusGroup_product_mem n hn)) z (unitHeckeProductSL_boundary_fixed n hn)
    simpa only [unitHeckeProductSL_order] using h
  have hh:=mobius_pointOrder_height G P.discrete hT hp z (hn.trans hl)
  have hz : z.im=Real.tan (Real.pi/(n:ℝ))/2:=by
    change (unitHeckeCorner n hn).im=_
    rw [unitHeckeCorner_im]
    ring
  apply le_antisymm _ hl
  by_contra hnot
  have hnm : (n:ℝ)<fordPointOrder G z:=by exact_mod_cast (lt_of_not_ge hnot)
  have hnR : (3:ℝ)≤n:=by exact_mod_cast hn
  have hmR : (3:ℝ)≤fordPointOrder G z:=le_trans hnR (by exact_mod_cast hl)
  have hna:=pi_div_acute_of_two_lt n (by linarith only [hnR])
  have hma:=pi_div_acute_of_two_lt (fordPointOrder G z) (by linarith only [hmR])
  have harg : Real.pi/fordPointOrder G z<Real.pi/(n:ℝ):=
    div_lt_div_of_pos_left Real.pi_pos (by linarith only [hnR]) hnm
  have ht:=Real.strictMonoOn_tan
    (show Real.pi/fordPointOrder G z∈Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hma.1,hma.2,Real.pi_pos])
    (show Real.pi/(n:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hna.1,hna.2,Real.pi_pos]) harg
  rw [hz] at hh
  linarith only [hh,ht]

/-- Every actual supergroup image of the sharp corner has at most its original height. -/
theorem finiteHecke_supergroup_corner_maxheight (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) :
    (A•unitHeckeCorner n hn).im≤(unitHeckeCorner n hn).im := by
  have ho:=fordPointOrder_realSL_orbit G A hA (unitHeckeCorner n hn)
  rw [finiteHecke_supergroup_corner_order n hn G P hsub] at ho
  have hh:=mobius_pointOrder_height G P.discrete
    (hsub (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)))
    (fun f hf=>P.preserves ⟨f,hf⟩) (A•unitHeckeCorner n hn) (by rwa [ho])
  rw [ho] at hh
  rw [unitHeckeCorner_im]
  linarith only [hh]

/-- The actual sharp Hecke corner belongs to the genuine whole-supergroup Ford exterior. -/
theorem finiteHecke_supergroup_corner_exterior (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup) (P : HalfPlaneFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    unitHeckeCorner n hn∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior G := by
  intro A
  exact (parabolicFord_im_le_iff_denominator A.val _).mp
    (finiteHecke_supergroup_corner_maxheight n hn G P hsub A.val A.property)

/-- Two true equal-height corner inequalities control the full hyperbolic region above their joining circle. -/
theorem hecke_denominator_two_corners (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : ℍ) (hw : w.re=(1:ℝ)/2)
    (hp : 1≤‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A w‖)
    (hm : 1≤‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)•w)‖)
    (z : ℍ) (hx : |z.re|≤(1:ℝ)/2) (hnorm : Complex.normSq (w:ℂ)≤Complex.normSq (z:ℂ)) :
    1≤‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z‖ := by
  have hp' : 1≤Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A w) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [hp]
  have hm' : 1≤Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)•w)) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [hm]
  have hre : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)•w).re= -1/2 := by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)•w:ℍ):ℂ).re=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp only [Complex.add_re,UpperHalfPlane.coe_re,Complex.ofReal_re]
    linarith only [hw]
  have him : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)•w).im=w.im:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im _ _
  rw [realSLDenominator_normSq,hw] at hp'
  rw [realSLDenominator_normSq,hre,him] at hm'
  have hN : w.re^2+w.im^2≤z.re^2+z.im^2 := by
    simpa only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two] using hnorm
  rw [hw] at hN
  have hΔ : 0≤(A 1 0)^2*((z.re^2+z.im^2)-((1/2:ℝ)^2+w.im^2)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hN)
  have hlow:= (abs_le.mp hx).1
  have hupp:= (abs_le.mp hx).2
  have hs : 1≤Complex.normSq (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z) := by
    rw [realSLDenominator_normSq]
    rcases le_total 0 (A 1 0*A 1 1) with hcd|hcd
    · have hlin : 0≤2*(A 1 0*A 1 1)*(z.re+1/2) :=
        mul_nonneg (mul_nonneg (by norm_num) hcd) (by linarith only [hlow])
      nlinarith only [hm',hΔ,hlin]
    · have hlin : 0≤2*(-(A 1 0*A 1 1))*(1/2-z.re) :=
        mul_nonneg (mul_nonneg (by norm_num) (neg_nonneg.mpr hcd)) (by linarith only [hupp])
      nlinarith only [hp',hΔ,hlin]
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith only [hs,norm_nonneg (_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator A z)]

end LowDimensionalTopology.Geometry.Fuchsian
