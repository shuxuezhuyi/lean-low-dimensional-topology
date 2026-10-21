module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusOrbitLimits
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- Every ordinary-point stabilizer of a discrete Möbius subgroup is finite cyclic. -/
theorem ordinary_point_stabilizer_finite_cyclic (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (z : Mobius.ExtendedComplex) (hz : z ∈ mobiusOrdinarySet H) :
    Finite (MulAction.stabilizer H z) ∧ IsCyclic (MulAction.stabilizer H z) := by
  have hD := mobius_ordinary_discontinuous H hH hd
  have hfin := hD.finite_stabilizer z hz
  let K := mobiusBoundaryStabilizer H z
  let : Finite K := (mobiusBoundaryStabilizer_finite H hD z hz).to_subtype
  let : IsCyclic K := finiteMobius_fix_boundary_isCyclic K z
    (fun f hf => ((mem_mobiusBoundaryStabilizer H z f).mp hf).2)
  let e : MulAction.stabilizer H z ≃* K :=
    (MulAction.stabilizer H z).equivMapOfInjective H.subtype Subtype.val_injective
  exact ⟨hfin.to_subtype, isCyclic_of_injective e.toMonoidHom e.injective⟩

/--
The actual ordinary set has genuine invariant separating
round-disc neighborhoods, with their closures still in the ordinary set.
-/
theorem exists_invariant_disc_neighbourhood_disjoint_other_translates (H : Subgroup Mobius.complexMobiusGroup) (hH
    : IsNonElementary H)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (z : Mobius.ExtendedComplex) (hz : z ∈ mobiusOrdinarySet H) :
    ∃ N : Set Mobius.ExtendedComplex, Mobius.IsComplexOpenDisc N ∧ z ∈ N ∧ closure N ⊆ mobiusOrdinarySet H ∧
      ∀ g : H,
        (g • z = z → (fun w : Mobius.ExtendedComplex => g • w) '' N = N) ∧
        (g • z ≠ z → Disjoint ((fun w : Mobius.ExtendedComplex => g • w) '' N) N) := by
  obtain ⟨q, r, _hr, _hq, hN, hzN, hcl, _hrot, hsep⟩ :=
    mobius_discontinuous_roundDisc H (mobiusOrdinarySet H) (mobiusOrdinarySet_isOpen H)
      (fun g _ hw => mobiusOrdinarySet_invariant H g hw)
      (mobius_ordinary_discontinuous H hH hd) z hz
  exact ⟨mobiusNormalizedDisc q r, hN, hzN, hcl, hsep⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
