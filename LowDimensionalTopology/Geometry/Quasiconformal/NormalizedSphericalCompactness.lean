module

public import LowDimensionalTopology.External.LiZhongQC.Ch05.S21_UniversalTeichmuller
public import LowDimensionalTopology.Geometry.Mobius.Metric.ChordalIsometries
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Global spherical compactness of the original normalized plane maps

The existing normalized family, its same-K limit and uniform properness bound
are Wu Xiaobin's LiZhongQC APIs, Apache-2.0, pinned upstream
`1c0d5473c020b66ed5106331a38a61536760b9b2`, in
`Ch05/S21_UniversalTeichmuller.lean`; see `THIRD_PARTY_NOTICES.md`.
The spherical metric is the existing actual sphere-induced chordal metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LiZhongQC

private theorem chordal_le_twice_dist (z w : ℂ) :
    Mobius.complexChordalDist (z : Mobius.ExtendedComplex) w ≤ 2 * dist z w := by
  have hz : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖])
  have hw : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖w‖])
  have hd : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hw)]
  rw [Mobius.complexChordalDist_coe_coe, dist_eq_norm]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
  nlinarith [norm_nonneg (z - w)]

/-- The actual normalized-family properness estimate upgrades local convergence
to uniform convergence on the WHOLE plane in the original sphere metric. -/
theorem normalized_locallyUniform_tendstoUniformly_chordal
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K : ℝ}
    (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (hlim : TendstoLocallyUniformly F G atTop) :
    let := Mobius.complexChordalMetricSpace
    TendstoUniformly (fun n z => (F n z : Mobius.ExtendedComplex))
      (fun z => (G z : Mobius.ExtendedComplex)) atTop := by
  let := Mobius.complexChordalMetricSpace
  have hG := UniversalTeichmuller.ut2_nf_limit hF hlim
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let R : ℝ := 8 / ε
  have hR : 0 < R := by dsimp [R]; positivity
  let L : ℝ := lambdaInv (K * quadLambda R)
  have hfar (w : ℂ) (hw : R ≤ ‖w‖) :
      Mobius.complexChordalDist (w : Mobius.ExtendedComplex) ∞ ≤ ε / 4 := by
    have hs : R ≤ Real.sqrt (1 + ‖w‖ ^ 2) :=
      hw.trans (Real.le_sqrt_of_sq_le (by nlinarith))
    rw [Mobius.complexChordalDist_coe_infty]
    calc
      2 / Real.sqrt (1 + ‖w‖ ^ 2) ≤ 2 / R :=
        div_le_div_of_nonneg_left (by norm_num) hR hs
      _ = ε / 4 := by
        dsimp [R]
        field_simp [hε.ne']
        ring
  have hcompact : TendstoUniformlyOn F G atTop (closedBall (0 : ℂ) L) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hlim) _ (isCompact_closedBall _ _)
  rw [Metric.tendstoUniformlyOn_iff] at hcompact
  filter_upwards [hcompact (ε / 4) (by positivity)] with n hn z
  change Mobius.complexChordalDist (G z : Mobius.ExtendedComplex) (F n z) < ε
  by_cases hz : ‖z‖ ≤ L
  · have he := hn z (mem_closedBall_zero_iff.mpr hz)
    exact (chordal_le_twice_dist (G z) (F n z)).trans_lt (by linarith)
  · have htail : lambdaInv (K * quadLambda R) < ‖z‖ := lt_of_not_ge hz
    have hFn := bA_w2_proper (hF n) hR htail
    have hGn := bA_w2_proper hG hR htail
    calc
      Mobius.complexChordalDist (G z : Mobius.ExtendedComplex) (F n z) ≤
          Mobius.complexChordalDist (G z : Mobius.ExtendedComplex) ∞ +
            Mobius.complexChordalDist ∞ (F n z : Mobius.ExtendedComplex) :=
        dist_triangle _ _ _
      _ = Mobius.complexChordalDist (G z : Mobius.ExtendedComplex) ∞ +
          Mobius.complexChordalDist (F n z : Mobius.ExtendedComplex) ∞ := by
        rw [Mobius.complexChordalDist_comm ∞]
      _ ≤ ε / 4 + ε / 4 := add_le_add (hfar _ hGn.le) (hfar _ hFn.le)
      _ < ε := by linarith

/-- Every normalized plane family has a globally spherical convergent subsequence,
retaining the same K and both original normalizations. -/
theorem normalized_plane_spherical_compactness
    {F : ℕ → ℂ → ℂ} {K : ℝ}
    (hF : ∀ n, IsKQCNormalizedPlane (F n) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      IsKQCNormalizedPlane G K ∧
      let := Mobius.complexChordalMetricSpace
      TendstoUniformly (fun n z => (F (φ n) z : Mobius.ExtendedComplex))
        (fun z => (G z : Mobius.ExtendedComplex)) atTop := by
  obtain ⟨φ, hφ, G, hlim⟩ := UniversalTeichmuller.ut2_nf_extract hF
  refine ⟨φ, hφ, G, UniversalTeichmuller.ut2_nf_limit (fun n => hF (φ n)) hlim, ?_⟩
  exact normalized_locallyUniform_tendstoUniformly_chordal (fun n => hF (φ n)) hlim

/-- Any spherical uniform limit of the original normalized family is finite
everywhere and is again an onto normalized plane map with the SAME K. -/
theorem normalized_plane_spherical_limit
    {F : ℕ → ℂ → ℂ} {K : ℝ}
    (hF : ∀ n, IsKQCNormalizedPlane (F n) K)
    (H : ℂ → Mobius.ExtendedComplex)
    (hlim : letI := Mobius.complexChordalMetricSpace
      TendstoUniformly (fun n z => (F n z : Mobius.ExtendedComplex)) H atTop) :
    ∃ G : ℂ → ℂ, IsKQCNormalizedPlane G K ∧
      ∀ z : ℂ, H z = (G z : Mobius.ExtendedComplex) := by
  let := Mobius.complexChordalMetricSpace
  obtain ⟨φ, hφ, G, hG, hGlim⟩ := normalized_plane_spherical_compactness hF
  refine ⟨G, hG, fun z => ?_⟩
  exact tendsto_nhds_unique ((hlim.tendsto_at z).comp hφ.tendsto_atTop)
    (hGlim.tendsto_at z)

end LowDimensionalTopology.Geometry.Quasiconformal
