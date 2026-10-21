/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Trace.HalfTurnTraces
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem axisHalfTurnSL_boundary_pair (a : ℝ) (ha : 0<a) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha)).val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)={((0:ℂ):Mobius.ExtendedComplex),∞} := by
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha)
  have hi : f.val ∞=(0:ℂ) := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha)).val ∞=(0:ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,Matrix.SpecialLinearGroup.toGL,Matrix.SpecialLinearGroup.map,
      Complex.ofReal_ne_zero.mpr ha.ne']
  have htwo : f^2=1 := by
    rw [←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at a ha).1]
    exact pow_orderOf_eq_one f
  have htwopt (z : Mobius.ExtendedComplex) : f.val (f.val z)=z := by
    change (f^2).val z=z
    rw [htwo]
    rfl
  have hz : f.val (0:ℂ)=∞ := by
    calc
      f.val (0:ℂ)=f.val (f.val ∞) := by rw [hi]
      _=∞ := htwopt ∞
  change f.val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)={((0:ℂ):Mobius.ExtendedComplex),∞}
  rw [Set.image_insert_eq,Set.image_singleton,hz,hi]
  exact Set.pair_comm _ _

theorem halfTurn_imaginary_center_boundary_pair (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : ℍ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A z) (hz : z.re=0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)={((0:ℂ):Mobius.ExtendedComplex),∞} := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 z.im z.im_pos=z :=
    UpperHalfPlane.ext_re_im hz.symm rfl
  have hJ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL z.im z.im_pos) z := by
    rw [←he]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at z.im z.im_pos
  rw [hA.unique hJ]
  exact axisHalfTurnSL_boundary_pair z.im z.im_pos

/-- Two actual imaginary images force every collinear original point to have imaginary image. -/
theorem collinear_third_imaginary
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (p q r : ℍ)
    (hpq : p≠q)
    (hp : p∈L.carrier) (hq : q∈L.carrier) (hr : r∈L.carrier)
    (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hQp : (Q•p).re=0) (hQq : (Q•q).re=0) :
    (Q•r).re=0 := by
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (isometry_smul ℍ Q) L
  have hpM : Q•p∈M.carrier := by rw [←hM];exact ⟨p,hp,rfl⟩
  have hqM : Q•q∈M.carrier := by rw [←hM];exact ⟨q,hq,rfl⟩
  have hrM : Q•r∈M.carrier := by rw [←hM];exact ⟨r,hr,rfl⟩
  have he : M=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 :=
    M.eq_of_two_points _ ((MulAction.injective Q).ne hpq) hpM hqM hQp hQq
  rw [he] at hrM
  exact hrM

theorem mobius_conjugate_pair_pullback (f Q : Mobius.complexMobiusGroup)
    (h : (Q*f*Q⁻¹).val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)={((0:ℂ):Mobius.ExtendedComplex),∞}) :
    f.val '' ({Q⁻¹.val (0:ℂ),Q⁻¹.val ∞} : Set Mobius.ExtendedComplex)={Q⁻¹.val (0:ℂ),Q⁻¹.val ∞} := by
  have he : Q⁻¹.val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)={Q⁻¹.val (0:ℂ),Q⁻¹.val ∞} := by
    rw [Set.image_insert_eq,Set.image_singleton]
  rw [←he]
  calc
    f.val '' (Q⁻¹.val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex))=
        Q⁻¹.val '' ((Q*f*Q⁻¹).val '' ({((0:ℂ):Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex)) := by
      rw [Set.image_image,Set.image_image]
      congr 1
      funext x
      change f•(Q⁻¹•x)=Q⁻¹•((Q*f*Q⁻¹)•x)
      simp only [mul_smul,inv_smul_smul]
    _=_ := by rw [h]

/-- The actual three-half-turn group is elementary whenever its actual centers are collinear. -/
theorem collinear_halfTurns_elementary
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (p q r : ℍ)
    (hpq : p≠q)
    (hp : p∈L.carrier) (hq : q∈L.carrier) (hr : r∈L.carrier)
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A p)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B q)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C r) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)) := by
  obtain ⟨Q,hQp,hQq,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_sl2_ordered_imaginary p q hpq
  have hQr:=collinear_third_imaginary L p q r hpq hp hq hr Q hQp hQq
  let P : Set Mobius.ExtendedComplex := {(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q)⁻¹.val (0:ℂ),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q)⁻¹.val ∞}
  have hmem (X : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ)
      (hX : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt X z) (hz : (Q•z).re=0) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X∈_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer ⊤ P := by
    refine ⟨by trivial,?_⟩
    apply mobius_conjugate_pair_pullback (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q)
    have he:=halfTurn_imaginary_center_boundary_pair (Q*X*Q⁻¹) (Q•z) (hX.conjugate Q) hz
    simpa only [map_mul,map_inv] using he
  have hsub : Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)≤
        _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer ⊤ P := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact hmem A p hA hQp
    · exact hmem B q hB hQq
    · exact hmem C r hC hQr
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_invariant_pair _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q)⁻¹.val (0:ℂ)) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q)⁻¹.val ∞)
  intro g
  exact (hsub g.property).2

/-- The original geometric half-turn group, with all real lifts constructed from the actual action. -/
theorem mobius_collinear_halfTurns_elementary
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (p q r : ℍ)
    (hpq : p≠q)
    (hp : p∈L.carrier) (hq : q∈L.carrier) (hr : r∈L.carrier)
    (f g h : Mobius.complexMobiusGroup)
    (hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hg : g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hh : h.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hf2 : orderOf f=2) (hg2 : orderOf g=2) (hh2 : orderOf h=2)
    (hfp : f.val (p:ℂ)=(p:ℂ)) (hgq : g.val (q:ℂ)=(q:ℂ)) (hhr : h.val (r:ℂ)=(r:ℂ)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)) := by
  obtain ⟨A,hA,hAt⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.geometric_halfTurn_lift_exists f p hf hf2 hfp
  obtain ⟨B,hB,hBt⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.geometric_halfTurn_lift_exists g q hg hg2 hgq
  obtain ⟨C,hC,hCt⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.geometric_halfTurn_lift_exists h r hh hh2 hhr
  simpa only [←hA,←hB,←hC] using collinear_halfTurns_elementary L p q r hpq hp hq hr A B C hAt hBt hCt

end LowDimensionalTopology.Geometry.Fuchsian
