/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPointHeights
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

def unitHeckeInversionSL (q : ℕ∞) (hq : 3≤q) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  unitHeckeDilationSL q hq*modularInversionSL*(unitHeckeDilationSL q hq)⁻¹

theorem unitHeckeInversionSL_native (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeInversionSL q hq)=unitHeckeInversion q hq := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_ * _⁻¹)=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _)⁻¹
  rw [map_mul,map_mul,map_inv]

def unitHeckeProductSL (n : ℕ) (hn : 3≤n) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*unitHeckeInversionSL n (by exact_mod_cast hn)

theorem unitHeckeProductSL_native (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeProductSL n hn)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*unitHeckeInversion n (by exact_mod_cast hn) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_) = _
  rw [map_mul]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeInversionSL n (by exact_mod_cast hn))=_
  rw [unitHeckeInversionSL_native]

theorem unitHeckeMobiusGroup_translation_mem (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈unitHeckeMobiusGroup q hq := by
  rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation]
  apply nativeConformalSubgroupMobiusGroup_matrix_mem
  rw [unitHeckeGroup_generators]
  exact Subgroup.subset_closure (by simp)

theorem unitHeckeMobiusGroup_product_mem (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)∈unitHeckeMobiusGroup n (by exact_mod_cast hn) := by
  apply nativeConformalSubgroupMobiusGroup_matrix_mem
  rw [unitHeckeProductSL_native,unitHeckeGroup_generators]
  exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

theorem unitHeckeProductSL_order (n : ℕ) (hn : 3≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn))=n := by
  rw [realSLMobius_order_eq_native,unitHeckeProductSL_native]
  exact unitHeckeProduct_order n hn

theorem unitHeckeProductSL_fixed (n : ℕ) (hn : 3≤n) :
    unitHeckeProductSL n hn • unitHeckeCorner n hn=unitHeckeCorner n hn := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeProductSL n hn) (unitHeckeCorner n hn)=_
  rw [unitHeckeProductSL_native]
  exact unitHeckeCorner_fixed n hn

theorem unitHeckeProductSL_elliptic (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_of_fixed _ _ _ (unitHeckeProductSL_fixed n hn)
  intro he
  have ho:=unitHeckeProductSL_order n hn
  rw [he,orderOf_one] at ho
  omega

theorem unitHeckeProductSL_boundary_fixed (n : ℕ) (hn : 3≤n) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (unitHeckeCorner n hn))=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (unitHeckeCorner n hn) := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn)).val
    (((unitHeckeCorner n hn:ℍ):ℂ):Mobius.ExtendedComplex)=(((unitHeckeCorner n hn:ℍ):ℂ):Mobius.ExtendedComplex)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,unitHeckeProductSL_fixed]

theorem unitHeckeCorner_order (n : ℕ) (hn : 3≤n) :
    fordPointOrder (unitHeckeMobiusGroup n (by exact_mod_cast hn)) (unitHeckeCorner n hn)=n := by
  let G:=unitHeckeMobiusGroup n (by exact_mod_cast hn)
  let P:=unitHeckeMobiusData n (by exact_mod_cast hn)
  let z:=unitHeckeCorner n hn
  have hp : ∀f∈G,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=fun f hf=>P.preserves ⟨f,hf⟩
  have hl : n≤fordPointOrder G z:=by
    have h:=elliptic_order_le_fordPointOrder G P.discrete hp _
      (unitHeckeMobiusGroup_product_mem n hn) z (unitHeckeProductSL_boundary_fixed n hn)
    simpa only [unitHeckeProductSL_order] using h
  have hh:=mobius_pointOrder_height G P.discrete (unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn)) hp z (hn.trans hl)
  have hz : z.im=Real.tan (Real.pi/(n:ℝ))/2:=by
    change (unitHeckeCorner n hn).im=Real.tan (Real.pi/(n:ℝ))/2
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
  linarith


theorem unitHeckeCorner_translation_half_displacement (n : ℕ) (hn : 3≤n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (unitHeckeCorner n hn)=
      Real.cot (Real.pi/(n:ℝ)) := by
  change Real.sinh (dist (unitHeckeCorner n hn) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•unitHeckeCorner n hn)/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement,unitHeckeCorner_im]
  norm_num only [abs_one]
  rw [←Real.tan_inv_eq_cot,inv_eq_one_div]
  congr 1
  ring

theorem unitHecke_sharp_height_witness (n : ℕ) (hn : 3≤n) :
    let G:=unitHeckeMobiusGroup n (by exact_mod_cast hn)
    HalfPlaneFuchsianGroup G ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈G ∧
      ∃f∈G,∃z : ℍ,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f ∧ orderOf f=n ∧
        f.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z ∧
        fordPointOrder G z=n ∧ z.im=(1/2)*Real.tan (Real.pi/(n:ℝ)) ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z=Real.cot (Real.pi/(n:ℝ)) := by
  exact ⟨unitHeckeMobiusData n (by exact_mod_cast hn),
    unitHeckeMobiusGroup_translation_mem n (by exact_mod_cast hn),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeProductSL n hn),unitHeckeMobiusGroup_product_mem n hn,
    unitHeckeCorner n hn,unitHeckeProductSL_elliptic n hn,unitHeckeProductSL_order n hn,
    unitHeckeProductSL_boundary_fixed n hn,unitHeckeCorner_order n hn,
    unitHeckeCorner_im n hn,unitHeckeCorner_translation_half_displacement n hn⟩

end LowDimensionalTopology.Geometry.Fuchsian
