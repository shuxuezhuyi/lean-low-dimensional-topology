module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticDiscCyclicity
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup

/-!
# Actual cyclic models of hyperbolic surfaces with abelian fundamental group

The hypothesis concerns the fundamental group of the original arbitrary
surface at its given basepoint. Commutativity of its Fuchsian model is derived
through the actual quotient covering, with Mathlib's opposite-group convention.
The conformal quotient and all its original geometric hypotheses are retained.
-/

public section
noncomputable section

open Set

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry
open Hyperbolic Mobius DiscreteGroups DiscreteGroups.Action

/-- An arbitrary original hyperbolic-type surface with abelian fundamental
group has a genuine cyclic Fuchsian model. No compactness or genus is assumed. -/
theorem IsHyperbolicType.exists_cyclic_quotient_of_fundamentalGroup_commute
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (hR : IsHyperbolicType R) (x : X)
    (hcomm : ∀ a b : FundamentalGroup X x, Commute a b) :
    ∃ (H : Subgroup Mobius.complexMobiusGroup)
      (hInv : ∀ (g : H) z, z ∈ extendedUnitDisc → g • z ∈ extendedUnitDisc)
      (hD : IsMobiusDiscontinuousOn H extendedUnitDisc),
      (∀ g ∈ H, g ≠ 1 → ¬Mobius.MobiusElliptic g) ∧ IsCyclic H ∧
      RiemannConformallyEquivalent R
        (mobiusQuotientRiemannSurface (unitDiscMobiusInvariantDomain H hInv) hD) := by
  obtain ⟨H, hInv, hD, hno, f, hf, hbij⟩ := hR
  let D := unitDiscMobiusInvariantDomain H hInv
  let E := hf.toHomeomorph hbij
  let : SimplyConnectedSpace D.carrier := discRiemannSurface_simplyConnected
  let hp := mobiusDomain_noElliptic_covering D hD hno
  obtain ⟨z, hz⟩ := mobiusDomainProjection_surjective D (E x)
  let j : FundamentalGroup X x ≃* Hᵐᵒᵖ :=
    (fundamentalGroupHomeomorphMulEquiv E x).trans
      (hp.fundamentalGroupEquiv (x := E x) ⟨z, hz⟩)
  have hHcomm (a b : H) : Commute a b := by
    change a * b = b * a
    apply MulOpposite.op_injective
    rw [MulOpposite.op_mul, MulOpposite.op_mul]
    obtain ⟨A, hA⟩ := j.surjective (MulOpposite.op a)
    obtain ⟨B, hB⟩ := j.surjective (MulOpposite.op b)
    rw [← hA, ← hB, ← map_mul, ← map_mul, (hcomm B A).eq]
  have hdisc : HasInvariantComplexDisc H := by
    refine ⟨extendedUnitDisc, extendedUnitDisc_isComplexOpenDisc, ?_⟩
    intro g
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hInv g w hw
    · intro w hw
      exact ⟨g⁻¹ • w, hInv g⁻¹ w hw, smul_inv_smul g w⟩
  have hd : IsDiscreteMobiusSubgroup H :=
    isMobiusDiscontinuousOn_invariant_discrete H D.carrier D.invariant
      D.isConnected.nonempty hD
  have hn : ∀ g ∈ H, ¬Mobius.MobiusElliptic g := fun g hg he => hno g hg he.1 he
  have hc : IsCyclic H := discrete_abelian_noElliptic_invariantDisc_isCyclic H hd hdisc hHcomm hn
  exact ⟨H, hInv, hD, hno, hc, f, hf, hbij⟩

end LowDimensionalTopology.Geometry.Surfaces
