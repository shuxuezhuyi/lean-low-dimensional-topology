/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordEllipticHeights
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordHeightRepresentatives
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Conjugating a subgroup by one of its actual members leaves it unchanged. -/
theorem ford_inner_subgroupConjugate (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g∈H) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g H=H := by
  ext f
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg)
  · intro hf
    refine ⟨g⁻¹*f*g,H.mul_mem (H.mul_mem (H.inv_mem hg) hf) hg,?_⟩
    change g*(g⁻¹*f*g)*g⁻¹=f
    group

/-- The actual original point-stabilizer order is constant along every true
real special-linear orbit in the original Mobius group. -/
theorem fordPointOrder_realSL_orbit (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B∈H) (z : ℍ) :
    fordPointOrder H (B•z)=fordPointOrder H z := by
  have he:=primitive_boundaryStabilizer_conjugation H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B) ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [ford_inner_subgroupConjugate H _ hB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at he
  unfold fordPointOrder
  rw [he]
  exact (Nat.card_congr
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).toEquiv).symm

/-- Any actual elliptic element fixing the original point has order at most
the actual point-stabilizer cardinal. -/
theorem elliptic_order_le_fordPointOrder (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (z : ℍ)
    (hfix : f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    orderOf f≤fordPointOrder H z := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let : Finite K:=halfPlanePointStabilizer_finite H hd hpres z
  have hfK : f∈K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _
    f).mpr ⟨hf,hfix⟩
  have hdiv:=orderOf_dvd_natCard (⟨f,hfK⟩:K)
  have ho : orderOf (⟨f,hfK⟩:K)=orderOf f:=(orderOf_injective K.subtype Subtype.val_injective _).symm
  rw [ho] at hdiv
  exact Nat.le_of_dvd Nat.card_pos hdiv

/-- The sharp normalized elliptic height bound holds at every original point,
using a genuinely constructed same-orbit Ford representative of greater height. -/
theorem mobius_pointOrder_height (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (z : ℍ)
    (hq : 3≤fordPointOrder H z) : z.im≤Real.tan (Real.pi/fordPointOrder H z)/2 := by
  obtain ⟨B,hB,hle,hFord⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.exists_ford_exterior_orbit_representative H hd hT z
  have hord:=fordPointOrder_realSL_orbit H B hB z
  have hqB : 3≤fordPointOrder H (B•z):=by rwa [hord]
  have hb:=mobiusFordExterior_elliptic_point_height H hd hT hpres (B•z) hFord hqB
  rw [hord] at hb
  exact hle.trans hb

/-- No primitive-generator premise is needed: the actual order of any
original elliptic fixing the point gives the same sharp height inequality. -/
theorem mobius_elliptic_point_height (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (z : ℍ)
    (hfix : f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (hq : 3≤orderOf f) :
    z.im≤Real.tan (Real.pi/orderOf f)/2 := by
  have hle:=elliptic_order_le_fordPointOrder H hd hpres f hf z hfix
  have hb:=mobius_pointOrder_height H hd hT hpres z (hq.trans hle)
  have hqR : (3:ℝ)≤orderOf f:=by exact_mod_cast hq
  have hleR : (orderOf f:ℝ)≤fordPointOrder H z:=by exact_mod_cast hle
  have hqa:=pi_div_acute_of_two_lt (orderOf f) (by linarith only [hqR])
  have hNa:=pi_div_acute_of_two_lt (fordPointOrder H z) (by linarith only [hqR,hleR])
  have harg : Real.pi/fordPointOrder H z≤Real.pi/orderOf f:=
    div_le_div_of_nonneg_left Real.pi_pos.le (by linarith only [hqR]) hleR
  have htan:=Real.strictMonoOn_tan.monotoneOn
    (show Real.pi/fordPointOrder H z∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hNa.1,Real.pi_pos],hNa.2⟩)
    (show Real.pi/orderOf f∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hqa.1,Real.pi_pos],hqa.2⟩) harg
  exact hb.trans (div_le_div_of_nonneg_right htan (by norm_num))

/-- The equivalent genuine unit-parabolic half-displacement bound at every
actual original elliptic center, with its original transformation order. -/
theorem mobius_elliptic_point_parabolic_displacement (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (z : ℍ)
    (hfix : f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (hq : 3≤orderOf f) :
    Real.cot (Real.pi/orderOf f)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  have hb:=mobius_elliptic_point_height H hd hT hpres f hf z hfix hq
  have h:=unitTranslation_half_displacement_lower_of_height z (Real.tan (Real.pi/orderOf f)/2) hb
  have he : 1/(2*(Real.tan (Real.pi/orderOf f)/2))=Real.cot (Real.pi/orderOf f):=by
    rw [←Real.tan_inv_eq_cot,inv_eq_one_div]
    congr 1
    ring
  rwa [he] at h

/-- The source normalization applied directly to the genuine native center of
an arbitrary original real elliptic matrix. -/
theorem realSL_elliptic_center_height (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hpres : ∀ f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hq : 3≤orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)).im≤
      Real.tan (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))/2 := by
  apply mobius_elliptic_point_height H hd hT hpres (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A) hAH _ _ hq
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ _).mpr rfl]


end LowDimensionalTopology.Geometry.Fuchsian
