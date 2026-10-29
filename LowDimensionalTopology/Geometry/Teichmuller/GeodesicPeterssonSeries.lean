module

public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesRealMobius

/-!
# The original full-cyclic geodesic Petersson series

The series uses the original axis seed and the supplied representatives of
the full projective-cyclic right cosets in the original covering group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

variable (Γ : Subgroup Deck) (A : Deck)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (ρ : Quotient (QuotientGroup.rightRel
      (Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
        (Subgroup.zpowers (Hyperbolic.realSLMobius A)))) → Γ)

/-- The literal endpoint-seed sum over the full original cyclic cosets. -/
def peterssonSeries (z : ℂ) : ℂ :=
  ∑' u, seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
    (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2

/-- Evaluation retains the original endpoint seed and supplied coset section. -/
@[simp] theorem peterssonSeries_apply (z : ℂ) :
    peterssonSeries Γ A hA ht ρ z =
      ∑' u, seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
        (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2 := rfl

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
