/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.TypeOneGroups
public import LowDimensionalTopology.Geometry.Mobius.Topology

@[expose] public section
noncomputable section
open Set
open scoped Topology Matrix.Norms.Frobenius
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem mobiusNormalizedNorm_nonneg (f : Mobius.complexMobiusGroup) : 0≤Mobius.mobiusNormalizedNorm f := by
  obtain ⟨A,rfl⟩:=Mobius.mobiusSpecialLinearProjection_surjective f
  rw [Mobius.mobiusNormalizedNorm_specialLinearProjection]
  exact Auxiliary.Algebra.matrixNorm_nonneg _

theorem mobiusNormalizedNorm_mul_le (f g : Mobius.complexMobiusGroup) :
    Mobius.mobiusNormalizedNorm (f*g)≤Mobius.mobiusNormalizedNorm f*Mobius.mobiusNormalizedNorm g := by
  obtain ⟨A,rfl⟩:=Mobius.mobiusSpecialLinearProjection_surjective f
  obtain ⟨B,rfl⟩:=Mobius.mobiusSpecialLinearProjection_surjective g
  rw [← map_mul,Mobius.mobiusNormalizedNorm_specialLinearProjection,
    Mobius.mobiusNormalizedNorm_specialLinearProjection,Mobius.mobiusNormalizedNorm_specialLinearProjection]
  exact Auxiliary.Algebra.matrixNorm_mul_le _ _

theorem mobiusNormalizedNorm_inv (f : Mobius.complexMobiusGroup) :
    Mobius.mobiusNormalizedNorm f⁻¹=Mobius.mobiusNormalizedNorm f := by
  obtain ⟨A,rfl⟩:=Mobius.mobiusSpecialLinearProjection_surjective f
  rw [← map_inv,Mobius.mobiusNormalizedNorm_specialLinearProjection,
    Mobius.mobiusNormalizedNorm_specialLinearProjection,Mobius.specialLinear_matrixNorm_inv]

theorem common_H3_fixed_norm_bounded (H : Subgroup Mobius.complexMobiusGroup)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hq : ∀ f∈H,f • q=q) :
    ∃ R : ℝ,∀ f : H,Mobius.mobiusNormalizedNorm f.val≤R := by
  let u:=upperHalfSpacePointNormalizer q
  have hu : u • q=Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := upperHalfSpacePointNormalizer_smul q
  refine ⟨2*Mobius.mobiusNormalizedNorm u^2,?_⟩
  intro f
  have hf : (u*f.val*u⁻¹) • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
    rw [← hu]
    simp only [mul_smul,inv_smul_smul,hq f.val f.property]
  have hs:=(Mobius.mobius_fixJ_iff_norm (u*f.val*u⁻¹)).mp hf
  have hC : Mobius.mobiusNormalizedNorm (u*f.val*u⁻¹)≤2 := by
    nlinarith [mobiusNormalizedNorm_nonneg (u*f.val*u⁻¹)]
  calc
    Mobius.mobiusNormalizedNorm f.val=Mobius.mobiusNormalizedNorm (u⁻¹*(u*f.val*u⁻¹)*u) := by
      congr 1
      group
    _ ≤ Mobius.mobiusNormalizedNorm (u⁻¹*(u*f.val*u⁻¹))*Mobius.mobiusNormalizedNorm u :=
      mobiusNormalizedNorm_mul_le _ _
    _ ≤ (Mobius.mobiusNormalizedNorm u⁻¹*Mobius.mobiusNormalizedNorm (u*f.val*u⁻¹))*Mobius.mobiusNormalizedNorm u :=
      mul_le_mul_of_nonneg_right (mobiusNormalizedNorm_mul_le _ _) (mobiusNormalizedNorm_nonneg _)
    _ ≤ (Mobius.mobiusNormalizedNorm u*2)*Mobius.mobiusNormalizedNorm u := by
      rw [mobiusNormalizedNorm_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hC (mobiusNormalizedNorm_nonneg _))
        (mobiusNormalizedNorm_nonneg _)
    _ = _ := by ring

theorem discreteMobius_finite_of_bounded_norm (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hbound : ∃ R : ℝ,∀ f : H,Mobius.mobiusNormalizedNorm f.val≤R) :
    Finite H := by
  obtain ⟨R,hR⟩:=hbound
  have hfinite:=Mobius.discreteMobius_norm_sublevel_finite H hH R
  have he : {f : H | Mobius.mobiusNormalizedNorm f.val≤R}=univ := by
    ext f
    simp only [mem_ofPred_eq,mem_univ,iff_true]
    exact hR f
  rw [he] at hfinite
  exact finite_univ_iff.mp hfinite

theorem discreteMobius_finite_of_common_H3_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hq : ∀ f∈H,f • q=q) :
    Finite H :=
  discreteMobius_finite_of_bounded_norm H hH (common_H3_fixed_norm_bounded H q hq)

theorem discreteMobius_typeOne_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hT : HasFullTypeOneOrbit H) : Finite H := by
  obtain ⟨q,hq⟩:=(hasFullTypeOneOrbit_iff_common_H3_fixed H).mp hT
  exact discreteMobius_finite_of_common_H3_fixed H hH q hq

theorem discreteMobius_typeOne_finite_rotation_realization (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (hT : HasFullTypeOneOrbit H) :
    ∃ u : Mobius.complexMobiusGroup,∃ R : Subgroup Mobius.rotationGroupThree,
      Finite R ∧ DiscreteGroups.Action.Actions.subgroupConjugate u H=Mobius.rotationMobiusSubgroup R ∧ Nonempty (H
        ≃* R) := by
  have : Finite H:=discreteMobius_typeOne_finite H hH hT
  obtain ⟨u,R,hR,⟨e⟩⟩:=typeOne_conjugate_rotation_realization H hT
  exact ⟨u,R,Finite.of_surjective e e.surjective,hR,⟨e⟩⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
