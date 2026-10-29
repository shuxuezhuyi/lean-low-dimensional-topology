module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms

/-!
# Expansion of the actual final beta generator

The book's attracting infinity and repelling zero labels force the actual
determinant-one representative to be diagonal with expanding square coefficient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius DiscreteGroups

namespace NormalizedCanonicalFuchsianModel
variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

/-- The actual dynamically normalized final beta matrix is diagonal, and its
literal action multiplier is the square of its upper-left entry, greater than one.
Both determinant-one matrix signs satisfy the same conclusion. -/
theorem final_beta_diagonal_expanding (P : NormalizedCanonicalFuchsianModel hg e m) :
    P.matrices (finalHandle hg, 1) 0 1 = 0 ∧
    P.matrices (finalHandle hg, 1) 1 0 = 0 ∧
    1 < P.matrices (finalHandle hg, 1) 0 0 ^ 2 := by
  let B := P.matrices (finalHandle hg, 1)
  have hB : IsMobiusAttractingRepellingPair (realSLMobius B) ∞ (0 : ℂ) :=
    P.beta_attracting_repelling
  have hc : B 1 0 = 0 := (realSLMobius_fixed_infty_iff B).mp hB.2.1
  have hp := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom B)) 0).mp
      (show Mobius.fractionalLinear _ ((0 : ℂ) : ExtendedComplex) = (0 : ℂ) by
        simpa only [realSLMobius, MonoidHom.comp_apply,
          Mobius.invariantDisc_specialLinear_action] using hB.2.2.1)
  have hb : B 0 1 = 0 := by
    change (B 1 0 : ℂ) * (0 * 0) + ((B 1 1 : ℂ) - (B 0 0 : ℂ)) * 0 +
      -(B 0 1 : ℂ) = 0 at hp
    have hz : (B 0 1 : ℂ) = 0 := by simpa using hp
    exact Complex.ofReal_eq_zero.mp hz
  have hd : B 0 0 * B 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] using B.property
  have hd0 : B 1 1 ≠ 0 := by intro hz; rw [hz, mul_zero] at hd; norm_num at hd
  obtain ⟨k, hk, hscale⟩ := realSLMobius_zero_infty_dilation B hB.2.2.1 hB.2.1
  let u : ℂˣ := Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')
  have hratio : B 0 0 / B 1 1 = k := by
    have he := congrArg (fun f : complexMobiusGroup => f.val ((1 : ℂ) : ExtendedComplex)) hscale
    rw [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action,
      Mobius.fractionalLinear_coe, Mobius.mobiusScaling_coe] at he
    change (if (B 1 0 : ℂ) * 1 + (B 1 1 : ℂ) = 0 then ∞ else
      (((B 0 0 : ℂ) * 1 + (B 0 1 : ℂ)) /
        ((B 1 0 : ℂ) * 1 + (B 1 1 : ℂ)) : ℂ)) = (((k : ℂ) * 1 : ℂ) : ExtendedComplex) at he
    simp only [hc, hb, Complex.ofReal_zero, zero_add, mul_one, add_zero] at he
    rw [ite_eq_right (Complex.ofReal_ne_zero.mpr hd0)] at he
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_div] using OnePoint.coe_injective he)
  have hsq : k = B 0 0 ^ 2 := by
    rw [← hratio]
    apply (div_eq_iff hd0).mpr
    calc
      B 0 0 = B 0 0 * (B 0 0 * B 1 1) := by rw [hd, mul_one]
      _ = B 0 0 ^ 2 * B 1 1 := by ring
  have hlim := hB.2.2.2.1 ((1 : ℂ) : ExtendedComplex)
    (fun he => one_ne_zero (OnePoint.coe_injective he))
  have hk1 : k ≠ 1 := by
    intro he
    have hu : u = 1 := by apply Units.ext; simp [u, he]
    have hmap : realSLMobius B = 1 := by
      change realSLMobius B = mobiusScaling u at hscale
      rw [hscale, hu, mobiusScaling_one]
    simp [hmap] at hlim
  have hkbig : 1 < k := by
    by_contra hn
    have hlt : k < 1 := lt_of_le_of_ne (not_lt.mp hn) hk1
    have hu1 : (u : ℂ) ≠ 1 := by
      intro he
      apply hk1
      simpa [u] using congrArg Complex.re he
    have hnorm : ‖(u : ℂ)‖ < 1 := by
      change ‖(k : ℂ)‖ < 1
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    have hstd : realSLMobius B = mobiusStandardElement u :=
      hscale.trans (mobiusScaling_eq_standard u hu1)
    have hz := (mobius_standard_contraction_attracting_repelling u hnorm).2.2.2.1
      ((1 : ℂ) : ExtendedComplex) (OnePoint.coe_ne_infty _)
    rw [← hstd] at hz
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique hz hlim)
  exact ⟨hb, hc, by simpa only [hsq] using hkbig⟩

end NormalizedCanonicalFuchsianModel
end LowDimensionalTopology.Geometry.Teichmuller
