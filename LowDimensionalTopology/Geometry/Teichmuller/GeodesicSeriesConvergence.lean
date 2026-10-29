module

public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.BersRealMobiusIsometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Actual convergence of the original endpoint geodesic series

The same actual conjugation and right-coset equivalence transport the proved
norm summability of the normalized full-period series. The termwise formula,
rather than equality of default sums, therefore proves the genuine HasSum
and absolute convergence on the original prescribed group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open GammaMeasurableBeltrami

/-- Every actual section of the full original cyclic right cosets has a
genuinely convergent endpoint series and summable norms on the upper half-plane. -/
theorem geodesicSeries_hasSum_norm
    (Γ : Subgroup Deck) (hΓ : LiZhongQC.IsFuchsian Γ) (A : Deck) (hAΓ : A ∈ Γ)
    (hA : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
      (Subgroup.zpowers (Hyperbolic.realSLMobius A))
    let CA := Quotient (QuotientGroup.rightRel SA)
    ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
      ∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
        HasSum (fun u : CA =>
          seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
            (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2)
          (∑' u : CA,
            seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
              (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2) ∧
        Summable (fun u : CA =>
          ‖seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
            (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2‖) := by
  dsimp only
  intro ρ hρ z hz
  obtain ⟨Q, s, hs, hQA⟩ := Fuchsian.realSLMobius_hyperbolic_positive_log_normal_form A
    ((Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr ht)
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
    (Subgroup.zpowers (Hyperbolic.realSLMobius A))
  let CA := Quotient (QuotientGroup.rightRel SA)
  let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
  obtain ⟨e, ρQ, _hmk, hρtransport, hρQ, _hseries⟩ :=
    geodesicSeries_realMobius_conjugate Γ A hA ht Q s hs hQA ρ hρ
  have hΓQ := LiZhongQC.s30l_isFuchsian_conj hΓ Q
  have hAQ : Q * A * Q⁻¹ ∈ ΓQ := Subgroup.mem_map.mpr ⟨A, hAΓ, rfl⟩
  have hrelative := AngularTwist.lengthKernel_relative_poincare ΓQ hΓQ
    (Q * A * Q⁻¹) hAQ s hs hQA ρQ hρQ
  let w : ℂ := LiZhongQC.h36p_m Q z
  have hw : w ∈ LiZhongQC.upperHalf := LiZhongQC.h36p_m_mem Q hz
  have hnormQ : Summable (fun v : CQ =>
      ‖(deriv (LiZhongQC.h36p_m (ρQ v).val) w / LiZhongQC.h36p_m (ρQ v).val w) ^ 2‖) :=
    (hrelative.1 w hw).2.1
  let d : ℂ := ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4
  have hterm (u : CA) :
      seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
          (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2 =
        (deriv (LiZhongQC.h36p_m (ρQ (e u)).val) w /
          LiZhongQC.h36p_m (ρQ (e u)).val w) ^ 2 / d := by
    rw [hρtransport]
    exact normalized_term A hA ht Q s hs hQA (ρ u).val hz
  have hnorm : Summable (fun u : CA =>
      ‖seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
        (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2‖) := by
    apply ((hnormQ.comp_injective e.injective).div_const ‖d‖).congr
    intro u
    rw [hterm u, norm_div]
    rfl
  exact ⟨hnorm.of_norm.hasSum, hnorm⟩

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
