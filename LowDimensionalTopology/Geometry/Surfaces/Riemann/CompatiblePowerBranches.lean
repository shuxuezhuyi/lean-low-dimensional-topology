/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic.FieldSimp

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology
open Filter
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A nonzero analytic unit has an actual analytic nth root near the point.
The root identity itself is global for the constructed function. -/
theorem analytic_unit_exists_root_at_zero (h : ℂ → ℂ) (ha : AnalyticAt ℂ h 0)
    (h0 : h 0 ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0 ≠ 0 ∧ ∀ z, R z ^ n = h z := by
  let c := (h 0) ^ ((n : ℂ)⁻¹)
  have hc : c ^ n = h 0 := Complex.cpow_nat_inv_pow _ hn
  have hcn : c ≠ 0 := by
    intro he
    rw [he, zero_pow hn] at hc
    exact h0 hc.symm
  let R : ℂ → ℂ := fun z => c * ((h z / h 0) ^ ((n : ℂ)⁻¹))
  have hu : AnalyticAt ℂ (fun z => h z / h 0) 0 := ha.div analyticAt_const h0
  have hslit : h 0 / h 0 ∈ Complex.slitPlane := by simp [h0]
  have hR : AnalyticAt ℂ R 0 := analyticAt_const.mul (hu.cpow analyticAt_const hslit)
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [R, div_self h0, Complex.one_cpow, mul_one] using hcn
  · intro z
    change (c * ((h z / h 0) ^ ((n : ℂ)⁻¹))) ^ n = h z
    rw [mul_pow, hc, Complex.cpow_nat_inv_pow _ hn]
    field_simp

/-- Analytic changes of coordinates fixing a branch value lift analytically
through two equal-degree power charts. The lifted derivative is nonzero as a
conclusion, not an additional branch-lifting hypothesis. -/
theorem analytic_local_coordinate_change_lifts_equal_powers
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 ≠ 0 ∧
      ∀ z, g z ^ n = f (z ^ n) := by
  let h := dslope f 0
  have hh : AnalyticAt ℂ h 0 := by
    obtain ⟨p, hp⟩ := hf
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have hh0 : h 0 ≠ 0 := by simpa only [h, dslope_same] using hdf
  obtain ⟨R, hR, hR0, hpow⟩ := analytic_unit_exists_root_at_zero h hh hh0 n hn
  let g : ℂ → ℂ := fun z => z * R (z ^ n)
  have hRn : AnalyticAt ℂ (fun z : ℂ => R (z ^ n)) 0 := by
    have hR' : AnalyticAt ℂ R ((0 : ℂ) ^ n) := by simpa only [zero_pow hn] using hR
    exact AnalyticAt.comp (f := fun z : ℂ => z ^ n) (x := (0 : ℂ)) hR' (analyticAt_id.pow n)
  have hg : AnalyticAt ℂ g 0 := analyticAt_id.mul hRn
  have hdg : HasDerivAt g (R 0) 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hlim : Tendsto (fun z : ℂ => R (z ^ n)) (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) := by
      simpa only [zero_pow hn] using hRn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzne : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    simp [slope, g, smul_eq_mul, hzne]
  refine ⟨g, hg, by simp [g], ?_, ?_⟩
  · rw [hdg.deriv]
    exact hR0
  · intro z
    change (z * R (z ^ n)) ^ n = f (z ^ n)
    rw [mul_pow, hpow]
    have hval := sub_smul_dslope f 0 (z ^ n)
    simpa only [sub_zero, hf0, smul_eq_mul, h] using hval

/-- The compatible lift is an actual local homeomorphism germ, as required
for normalizing the fiber product at an elliptically branched value. -/
theorem analytic_local_coordinate_change_power_homeomorph
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ G : OpenPartialHomeomorph ℂ ℂ, 0 ∈ G.source ∧ G 0 = 0 ∧
      AnalyticAt ℂ G 0 ∧ deriv G 0 ≠ 0 ∧ ∀ z, G z ^ n = f (z ^ n) := by
  obtain ⟨g, hg, hg0, hgn, hpow⟩ :=
    analytic_local_coordinate_change_lifts_equal_powers f hf hf0 hdf n hn
  have hgd := hg.hasStrictDerivAt.hasStrictFDerivAt_equiv hgn
  exact ⟨hgd.toOpenPartialHomeomorph g, hgd.mem_toOpenPartialHomeomorph_source,
    hg0, hg, hgn, hpow⟩

end LowDimensionalTopology.Geometry.Surfaces
