module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- The genuine finite value of an actual Mobius transformation fixing infinity. -/
def mobiusAffineFiniteValue (f : Mobius.mobiusInftyStabilizer) (z : ℂ) : ℂ :=
  (Mobius.mobiusMultiplier f : ℂ) * z + Mobius.mobiusAffineConstant f

/-- Evaluation at a finite point is continuous in the original Mobius topology. -/
theorem mobiusAffineFiniteValue_continuous (z : ℂ) :
    Continuous (fun f : Mobius.mobiusInftyStabilizer => mobiusAffineFiniteValue f z) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  have h := (Mobius.mobiusLocal_eval_continuous (z : Mobius.ExtendedComplex)).comp
    (continuous_subtype_val : Continuous (Subtype.val : Mobius.mobiusInftyStabilizer → Mobius.complexMobiusGroup))
  convert h using 1
  funext f
  exact (Mobius.mobius_affine_formula f z).symm

theorem mobiusAffineConstant_continuous : Continuous Mobius.mobiusAffineConstant := by
  convert mobiusAffineFiniteValue_continuous 0 using 1
  funext f
  simp only [mobiusAffineFiniteValue, mul_zero, zero_add]

theorem mobiusMultiplier_coe_continuous :
    Continuous (fun f : Mobius.mobiusInftyStabilizer => (Mobius.mobiusMultiplier f : ℂ)) := by
  have h := (mobiusAffineFiniteValue_continuous 1).sub mobiusAffineConstant_continuous
  convert h using 1
  funext f
  change (Mobius.mobiusMultiplier f : ℂ) = mobiusAffineFiniteValue f 1 - Mobius.mobiusAffineConstant f
  simp only [mobiusAffineFiniteValue, mul_one, add_sub_cancel_right]

/-- The two original affine parameters uniquely determine the actual Mobius transformation. -/
theorem mobius_affine_parameters_injective : Function.Injective
    (fun f : Mobius.mobiusInftyStabilizer => ((Mobius.mobiusMultiplier f : ℂ), Mobius.mobiusAffineConstant f)) := by
  intro f g h
  have ha : Mobius.mobiusMultiplier f = Mobius.mobiusMultiplier g := Units.ext (congrArg Prod.fst h)
  have hb : Mobius.mobiusAffineConstant f = Mobius.mobiusAffineConstant g := congrArg Prod.snd h
  apply Subtype.ext
  rw [Mobius.mobius_affine_representation f, Mobius.mobius_affine_representation g, ha, hb]

/-- Finite actual multipliers and discrete translation coefficients force discreteness in the
original Mobius topology. No unit-norm assumption is needed for this implication. -/
theorem affineLattice_discrete_of_finite_multiplier_values
    (H : Subgroup Mobius.complexMobiusGroup) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (L : AddSubgroup ℂ) [DiscreteTopology L]
    (hf : (Set.range (fun f : H => ((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ))).Finite)
    (hL : ∀ f : H, Mobius.mobiusAffineConstant ⟨f.val, hi f.property⟩ ∈ L) :
    Mobius.IsDiscreteMobiusSubgroup H := by
  let A := Set.range (fun f : H => ((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ))
  let : Finite A := hf.to_subtype
  let j : H → Mobius.mobiusInftyStabilizer := fun f => ⟨f.val, hi f.property⟩
  have hj : Continuous j := Continuous.subtype_mk continuous_subtype_val _
  let F : H → A × L := fun f =>
    (⟨(Mobius.mobiusMultiplier (j f) : ℂ), ⟨f, rfl⟩⟩, ⟨Mobius.mobiusAffineConstant (j f), hL f⟩)
  have hF : Continuous F := by
    exact (Continuous.subtype_mk (mobiusMultiplier_coe_continuous.comp hj) _).prodMk
      (Continuous.subtype_mk (mobiusAffineConstant_continuous.comp hj) _)
  have hFi : Function.Injective F := by
    intro f g h
    apply Subtype.ext
    have hp := congrArg (fun p : A × L => (p.1.val, p.2.val)) h
    exact congrArg (fun a : Mobius.mobiusInftyStabilizer => a.val) (mobius_affine_parameters_injective hp)
  exact DiscreteTopology.of_continuous_injective hF hFi

/-- The subgroup-valued finite-multiplier form used by actual crystallographic constructions. -/
theorem affineLattice_discrete (H : Subgroup Mobius.complexMobiusGroup) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (L : AddSubgroup ℂ) [DiscreteTopology L]
    (hf : (Mobius.subgroupMultiplierRange H hi : Set ℂˣ).Finite)
    (hL : ∀ f : H, Mobius.mobiusAffineConstant ⟨f.val, hi f.property⟩ ∈ L) :
    Mobius.IsDiscreteMobiusSubgroup H := by
  apply affineLattice_discrete_of_finite_multiplier_values H hi L _ hL
  apply (hf.image (fun a : ℂˣ => (a : ℂ))).subset
  rintro _ ⟨f, rfl⟩
  exact ⟨Mobius.subgroupMultiplierHom H hi f, ⟨f, rfl⟩, rfl⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
