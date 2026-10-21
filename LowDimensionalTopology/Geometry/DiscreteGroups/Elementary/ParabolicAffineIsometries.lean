/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteElementaryGroups
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem mobiusMultiplier_norm_eq_one_of_not_loxodromic (f : Mobius.mobiusInftyStabilizer)
    (hf : ¬Mobius.MobiusLoxodromic f.val) : ‖(Mobius.mobiusMultiplier f : ℂ)‖=1 := by
  by_cases h1 : f.val=1
  · have he : f=1 := Subtype.ext h1
    rw [he,Mobius.mobius_affine_parameters_one.1,Units.val_one,norm_one]
  rcases Mobius.mobius_nonidentity_type_trichotomy f.val h1 with hp | hL | he
  · rw [(mobiusMultiplier_eq_one_iff_parabolic_or_identity f).mpr (Or.inl hp),Units.val_one,norm_one]
  · exact False.elim (hf hL)
  · obtain ⟨q,hq⟩ := (Mobius.mobiusElliptic_iff_H3_fixed f.val h1).mp he
    have hh := congrArg (fun r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      Hyperbolic.QuaternionHalfSpace.quaternionHeight r.val) hq
    have hr := Mobius.mobius_affine_representation f
    change f.val = Mobius.affineMobius (Mobius.mobiusMultiplier f) (Mobius.mobiusAffineConstant f)
      (Units.ne_zero (Mobius.mobiusMultiplier f)) at hr
    rw [hr,Mobius.affineMobius_smul,Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint] at hh
    exact (mul_eq_right₀ q.property.ne').mp hh

theorem mobius_infty_stabilizer_isometry_of_not_loxodromic (f : Mobius.mobiusInftyStabilizer)
    (hf : ¬Mobius.MobiusLoxodromic f.val) :
    Isometry (fun z : ℂ => Mobius.finiteComplexPart f.val.val z) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [mobius_infty_stabilizer_finite_distance,mobiusMultiplier_norm_eq_one_of_not_loxodromic f hf,one_mul]

theorem mobius_infty_stabilizer_finite_formula (f : Mobius.mobiusInftyStabilizer) (z : ℂ) :
    Mobius.finiteComplexPart f.val.val z = (Mobius.mobiusMultiplier f:ℂ)*z+Mobius.mobiusAffineConstant f := by
  simp only [Mobius.finiteComplexPart,Mobius.mobius_affine_formula]
  rfl

theorem mobius_infty_stabilizer_finite_bijective (f : Mobius.mobiusInftyStabilizer) :
    Function.Bijective (Mobius.finiteComplexPart f.val.val) := by
  constructor
  · intro z w h
    rw [mobius_infty_stabilizer_finite_formula,mobius_infty_stabilizer_finite_formula] at h
    exact mul_left_cancel₀ (Units.ne_zero _) (add_right_cancel h)
  · intro w
    refine ⟨(w-Mobius.mobiusAffineConstant f)/(Mobius.mobiusMultiplier f:ℂ),?_⟩
    rw [mobius_infty_stabilizer_finite_formula]
    field_simp
    ring

/-- The genuine finite-coordinate Euclidean isometry of an affine nonloxodromic map. -/
def mobiusEuclideanIsometry (f : Mobius.mobiusInftyStabilizer) (hf : ¬Mobius.MobiusLoxodromic f.val) : ℂ ≃ᵢ ℂ where
  toEquiv := Equiv.ofBijective _ (mobius_infty_stabilizer_finite_bijective f)
  isometry_toFun := mobius_infty_stabilizer_isometry_of_not_loxodromic f hf

theorem mobiusEuclideanIsometry_apply (f : Mobius.mobiusInftyStabilizer)
    (hf : ¬Mobius.MobiusLoxodromic f.val) (z : ℂ) :
    mobiusEuclideanIsometry f hf z=Mobius.finiteComplexPart f.val.val z := rfl

theorem discrete_elementary_parabolic_euclidean_coordinates (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hE : IsElementary H) (p : Mobius.complexMobiusGroup)
    (hpH : p ∈ H) (hp : Mobius.MobiusParabolic p) :
    ∃ q : Mobius.complexMobiusGroup, ∃ hK : DiscreteGroups.Action.Actions.subgroupConjugate q H ≤
      Mobius.mobiusInftyStabilizer,
      ∀ f : DiscreteGroups.Action.Actions.subgroupConjugate q H,
        ‖((Mobius.subgroupMultiplierHom (DiscreteGroups.Action.Actions.subgroupConjugate q H) hK f : ℂˣ):ℂ)‖=1 ∧
        ∃ e : ℂ ≃ᵢ ℂ, ∀ z : ℂ, f.val.val (z:Mobius.ExtendedComplex)=(e z:ℂ) := by
  obtain ⟨a,_,hfix⟩ := elementary_parabolic_common_fixedPoint H hE p hpH hp
  obtain ⟨q,hK⟩ := mobius_common_fixed_conjugate_inftyStabilizer H a hfix
  refine ⟨q,hK,?_⟩
  intro f
  have hn : ¬Mobius.MobiusLoxodromic f.val := by
    obtain ⟨g,hg,hgf⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
    rw [← hgf,Mobius.mobiusLoxodromic_conjugation]
    exact discrete_elementary_parabolic_no_loxodromic H hD hE p hpH hp g hg
  refine ⟨mobiusMultiplier_norm_eq_one_of_not_loxodromic ⟨f.val,hK f.property⟩ hn,
    mobiusEuclideanIsometry ⟨f.val,hK f.property⟩ hn,?_⟩
  intro z
  rw [mobiusEuclideanIsometry_apply,mobius_infty_stabilizer_finite_formula]
  exact Mobius.mobius_affine_formula ⟨f.val,hK f.property⟩ z

end LowDimensionalTopology.Geometry.DiscreteGroups
