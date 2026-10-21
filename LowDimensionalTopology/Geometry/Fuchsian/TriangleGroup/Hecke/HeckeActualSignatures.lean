/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSignaturePatterns
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompletionConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicHeckeModels
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

/-- The genuine finite Hecke model has its actual genus, full elliptic class order multiset and one actual cusp. -/
theorem standardHecke_actual_signature (n:ℕ) (hn:3≤n) :
    HasCofiniteFuchsianSignature (standardHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc
      0 [2,n] 1 := by
  let T:=standardHeckeTriangle n (by exact_mod_cast hn)
  have hT:=standardHeckeTriangle_angles n (by exact_mod_cast hn)
  have hb:T.beta=Real.pi/(n:ℝ):=hT.2.1.trans (triangleOrderAngle_nat n)
  exact closedTriangle_actual_signature_one_ideal T 2 n (by omega) (by omega)
    hT.1 hb hT.2.2 (standardHeckeMobiusData n (by exact_mod_cast hn))

/-- The genuine infinite Hecke model has one actual order-two elliptic class and exactly two actual cusps. -/
theorem infinite_standardHecke_actual_signature :
    HasCofiniteFuchsianSignature (standardHeckeMobiusData ⊤ (by simp)).asFuchsianDisc 0 [2] 2 := by
  let T:=standardHeckeTriangle ⊤ (by simp)
  have hT:=standardHeckeTriangle_angles ⊤ (by simp)
  have hb:T.beta=0:=hT.2.1.trans triangleOrderAngle_top
  exact closedTriangle_actual_signature_two_ideal T 2 (by omega)
    hT.1 hb hT.2.2 (standardHeckeMobiusData ⊤ (by simp))



theorem realSLMobius_conjugation_of_native_eq (A B C:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C := by
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement A)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement C:=Subtype.ext h
  simpa only [map_mul,map_inv,halfPlaneConformalMobiusHom_matrix] using congrArg halfPlaneConformalMobiusHom he

theorem standardHeckeMobiusGroup_generators (q:ℕ∞) (hq:3≤q) :
    standardHeckeMobiusGroup q hq=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q))),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modularInversionSL}:Set Mobius.complexMobiusGroup) := by
  have hH:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q))),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL}:Set (ℍ≃ᵢℍ))≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=by
    rw [←standardHeckeGroup_generators]
    exact standardHeckeGroup_le_conformal q hq
  have h:=native_matrix_pair_mobius_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q))) modularInversionSL hH
  have hrange:∀(H K:Subgroup (ℍ≃ᵢℍ))
      (hH:H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (hK:K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup),H=K→
      (nativeConformalSubgroupMobiusHom H hH).range=(nativeConformalSubgroupMobiusHom K hK).range:=by
    intro H K hH hK he
    subst K
    rfl
  exact (hrange _ _ _ hH (standardHeckeGroup_generators q hq)).trans h

/-- Unit normalization is a literal whole-Mobius-group conjugacy by the genuine positive dilation. -/
theorem unitHeckeMobiusGroup_conjugation (q:ℕ∞) (hq:3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeDilationSL q hq)) (standardHeckeMobiusGroup q hq)=
      unitHeckeMobiusGroup q hq := by
  rw [standardHeckeMobiusGroup_generators,unitHeckeMobiusGroup_generators]
  change (Subgroup.closure _).map _=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
  have hT:=realSLMobius_conjugation_of_native_eq (unitHeckeDilationSL q hq)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) (unitHecke_translation q hq)
  have hS:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeDilationSL q hq)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modularInversionSL*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeDilationSL q hq))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL q hq):=by
    rw [unitHeckeInversionSL,map_mul,map_mul,map_inv]
  rw [hT,hS]



/-- The actual unit finite Hecke group retains the full geometric cofinite signature. -/
theorem unitHecke_actual_signature (n:ℕ) (hn:3≤n) :
    HasCofiniteFuchsianSignature (unitHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc 0 [2,n] 1 := by
  exact cofinite_signature_of_conjugate_group
    (standardHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc
    (unitHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeDilationSL n (by exact_mod_cast hn)))
    (unitHeckeMobiusGroup_conjugation n (by exact_mod_cast hn))
    (realSLMobius_image_openHalfPlane _) 0 1 [2,n] (standardHecke_actual_signature n hn)

theorem infinite_unitHecke_actual_signature :
    HasCofiniteFuchsianSignature (unitHeckeMobiusData ⊤ (by simp)).asFuchsianDisc 0 [2] 2 := by
  exact cofinite_signature_of_conjugate_group
    (standardHeckeMobiusData ⊤ (by simp)).asFuchsianDisc
    (unitHeckeMobiusData ⊤ (by simp)).asFuchsianDisc
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeDilationSL ⊤ (by simp)))
    (unitHeckeMobiusGroup_conjugation ⊤ (by simp))
    (realSLMobius_image_openHalfPlane _) 0 2 [2] infinite_standardHecke_actual_signature

end LowDimensionalTopology.Geometry.Fuchsian
