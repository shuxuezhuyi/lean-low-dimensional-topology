/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceAxioms
public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricSolutionContinuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual small comparisons for zero general QC distance

Zero distance supplies actual QC transitions between the prescribed original
targets. Their sharp maximal dilatations tend to one. Relative to any actual
uniformization of the first target, their symmetric normalized maps therefore
tend locally uniformly to the identity. No comparison sequence is supplied as
an extra assumption, and no compactness or extremal map is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

/-- The zero infimum gives genuine fixed-target comparisons and convergence of
their original symmetric normalized maps, with the comparisons chosen internally. -/
theorem exists_small_comparisons_of_distance_zero
    {R : Surface.{u}} (m n : Marked.{u, v} R)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → m.target.carrier} (hp : IsUniformization Γ p)
    (hzero : distance (mk m) (mk n) = 0) :
    ∃ f : ℕ → (m.target.carrier ≃ₜ n.target.carrier),
      (∀ j, IsQCRS (f j) ∧
        ContinuousMap.Homotopic
          ((m.marking.trans (f j) : R.carrier ≃ₜ n.target.carrier) :
            C(R.carrier, n.target.carrier))
          (n.marking : C(R.carrier, n.target.carrier)) ∧
        Real.log (maxDilatationRS (f j)).toReal < 1 / ((j : ℝ) + 1)) ∧
      TendstoLocallyUniformly
        (fun j z => s27u_fSym (s27u_liftCoeff p (f j)) z) (id : ℂ → ℂ) atTop := by
  have hex (j : ℕ) : ∃ f : m.target.carrier ≃ₜ n.target.carrier,
      IsQCRS f ∧
      ContinuousMap.Homotopic
        ((m.marking.trans f : R.carrier ≃ₜ n.target.carrier) :
          C(R.carrier, n.target.carrier))
        (n.marking : C(R.carrier, n.target.carrier)) ∧
      Real.log (maxDilatationRS f).toReal < 1 / ((j : ℝ) + 1) := by
    apply exists_comparison_of_distance_lt m n
    rw [hzero]
    positivity
  choose f hf hh hlog using hex
  refine ⟨f, fun j => ⟨hf j, hh j, hlog j⟩, ?_⟩
  let K : ℕ → ℝ := fun j => (maxDilatationRS (f j)).toReal
  have hK (j : ℕ) : 1 ≤ K j := s29_m_one_le_toReal (hf j)
  have hlogzero : Tendsto (fun j => Real.log (K j)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun j => Real.log_nonneg (hK j)) (fun j => (hlog j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hexplog (j : ℕ) : Real.exp (Real.log (K j)) = K j :=
    Real.exp_log (by linarith [hK j])
  have hKzero : Tendsto K atTop (𝓝 (1 : ℝ)) := by
    exact (Real.tendsto_exp_nhds_zero_nhds_one.comp hlogzero).congr hexplog
  let k : ℕ → ℝ := fun j => (K j - 1) / (K j + 1)
  have hk₀ (j : ℕ) : 0 ≤ k j :=
    div_nonneg (by linarith [hK j]) (by linarith [hK j])
  have hk (j : ℕ) : k j < 1 := by
    change (K j - 1) / (K j + 1) < 1
    apply (div_lt_one (by linarith [hK j])).2
    linarith
  have hkzero : Tendsto k atTop (𝓝 (0 : ℝ)) := by
    have hdiv : Tendsto ((fun j => K j - 1) / (fun j => K j + 1))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, one_add_one_eq_two, zero_div] using
        (hKzero.sub_const 1).div (hKzero.add_const 1) (by norm_num)
    exact hdiv.congr (fun _ => rfl)
  exact symmetricSolution_tendstoLocallyUniformly_zero
    (fun j => s27u_liftCoeff p (f j)) k hk₀ hk
    (fun j => s27u_liftCoeff_isBeltramiCoeff hp (s29_m_isKQCRS_maxDil (hf j))) hkzero

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
