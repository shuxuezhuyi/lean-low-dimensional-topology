module

public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMaps
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1Norm
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# Normalization to the literal book coefficient

Both source and target are the original closed surfaces. The parameter is a
positive real multiple of the original initial differential when the stretch is positive, and is zero at zero stretch.

Analytic APIs are from Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u

/-- Any actual geometric Teichmüller map has a parameter in the literal book L1
unit ball, whose book norm is exactly its stretch and whose actual Beltrami
coefficient is the normalized book formula. At zero stretch the parameter is zero. -/
theorem normalize_teichmullerMap_bookCoefficient
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {f : X ≃ₜ Y}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas}
    {q' : HolomorphicQuadraticDifferential S.toRiemannAtlas} {k : ℝ}
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsTeichmullerMap f q q' k) :
    ∃ φ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      φ ∈ QuadraticL1.openUnitBall R ∧ QuadraticL1.bookNorm R φ = k ∧
        (let := R.toRiemannAtlas.toChartedSpace
         let := S.toRiemannAtlas.toChartedSpace
         ∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain f x)),
           LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z =
             (QuadraticL1.bookNorm R φ : ℂ) * star ((φ : X → ℂ → ℂ) x z) /
               (‖(φ : X → ℂ → ℂ) x z‖ : ℂ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.connectedSpace
  let Q := HolomorphicQuadraticDifferential R.toRiemannAtlas
  let : NormedAddCommGroup Q := QuadraticL1.normedAddCommGroup R
  let : NormedSpace ℂ Q := QuadraticL1.normedSpace R
  have hzero : QuadraticL1.bookNorm R (0 : Q) = 0 := by
    rw [← QuadraticL1.norm_eq_bookNorm R (0 : Q), norm_zero]
  by_cases hk : k = 0
  · refine ⟨0, (QuadraticL1.mem_openUnitBall R 0).mpr (by rw [hzero]; norm_num),
      hzero.trans hk.symm, ?_⟩
    dsimp only
    intro x
    filter_upwards [(LiZhongQC.teichmullerMap_beltrami hf).1 x] with z hz
    simpa [LiZhongQC.teichmullerBeltrami, hk, hzero] using hz
  · have hkpos : 0 < k := lt_of_le_of_ne hf.k_nonneg (Ne.symm hk)
    have hqne : q ≠ 0 := fun h => hf.initial_ne (congrArg Subtype.val h)
    have hqpos : 0 < QuadraticL1.bookNorm R q := by
      have hn : 0 < ‖q‖ := norm_pos_iff.mpr hqne
      rw [QuadraticL1.norm_eq_bookNorm R q] at hn
      exact hn
    let c : ℝ := k / QuadraticL1.bookNorm R q
    have hc : 0 < c := div_pos hkpos hqpos
    let φ : Q := (c : ℂ) • q
    have hφnorm : QuadraticL1.bookNorm R φ = k := by
      calc
        QuadraticL1.bookNorm R φ = ‖φ‖ := (QuadraticL1.norm_eq_bookNorm R φ).symm
        _ = ‖(c : ℂ)‖ * ‖q‖ := norm_smul _ _
        _ = c * QuadraticL1.bookNorm R q := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
            QuadraticL1.norm_eq_bookNorm R q]
        _ = k := div_mul_cancel₀ k hqpos.ne'
    have hscaled := LiZhongQC.s29_e12_teichMap_smul hf hc
    have hμ := (LiZhongQC.teichmullerMap_beltrami hscaled).1
    refine ⟨φ, (QuadraticL1.mem_openUnitBall R φ).mpr (by rw [hφnorm]; exact hf.k_lt_one),
      hφnorm, ?_⟩
    dsimp only
    intro x
    filter_upwards [hμ x] with z hz
    simpa only [hφnorm, LiZhongQC.teichmullerBeltrami, φ,
      Submodule.coe_smul, starRingEnd_apply] using hz

end LowDimensionalTopology.Geometry.Teichmuller


namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

/-- A native analytic homeomorphism has the literal normalized book coefficient
at parameter zero on its unchanged original source and target. -/
theorem analytic_hasBookTeichmullerCoefficient_zero
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (ha : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f) :
    HasBookTeichmullerCoefficient R S f
      (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let Q := HolomorphicQuadraticDifferential R.toRiemannAtlas
  have hzero : QuadraticL1.bookNorm R (0 : Q) = 0 := by
    let : NormedAddCommGroup Q := QuadraticL1.normedAddCommGroup R
    rw [← QuadraticL1.norm_eq_bookNorm R (0 : Q), norm_zero]
  have hK := (LiZhongQC.isKQCRS_one_iff f).2
    ((analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas S.toRiemannAtlas f).mp ha)
  dsimp only [HasBookTeichmullerCoefficient]
  intro x
  filter_upwards [(LiZhongQC.isKQC_maxDilatation_le (hK.2 x)).2] with z hz
  have hnorm : ‖LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z‖ = 0 :=
    le_antisymm (by simpa using hz) (norm_nonneg _)
  have hμ : LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z = 0 :=
    norm_eq_zero.mp hnorm
  simpa only [hzero, Complex.ofReal_zero, zero_mul, zero_div] using hμ

/-- Every actual QC map between the original closed surfaces is homotopic to an
extremal map with a literal book-normalized L1 parameter on the original source.
The actual map is unique among extremals in that unchanged homotopy class. -/
theorem exists_unique_bookTeichmuller_extremal
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    ∃ (f₀ : X ≃ₜ Y) (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas),
      φ ∈ QuadraticL1.openUnitBall R ∧
      ContinuousMap.Homotopic (f : C(X, Y)) (f₀ : C(X, Y)) ∧
      HasBookTeichmullerCoefficient R S f₀ φ ∧
      LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ h : X ≃ₜ Y, LiZhongQC.IsExtremalInHomotopyClass h →
        ContinuousMap.Homotopic (f : C(X, Y)) (h : C(X, Y)) → h = f₀ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  obtain ⟨f₀, hhom, hkind, hext, huniq⟩ :=
    R.exists_unique_teichmuller_extremal S hg hgenus f hf
  rcases hkind with ha | ⟨q, q', k, hT⟩
  · have hzero : QuadraticL1.bookNorm R
        (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) = 0 := by
      let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
        QuadraticL1.normedAddCommGroup R
      rw [← QuadraticL1.norm_eq_bookNorm R 0, norm_zero]
    exact ⟨f₀, 0, (QuadraticL1.mem_openUnitBall R 0).mpr (by rw [hzero]; norm_num),
      hhom, analytic_hasBookTeichmullerCoefficient_zero R S f₀ ha, hext, huniq⟩
  · obtain ⟨φ, hφ, _, hμ⟩ := normalize_teichmullerMap_bookCoefficient R S hT
    exact ⟨f₀, φ, hφ, hhom, hμ, hext, huniq⟩

end LowDimensionalTopology.Geometry.Teichmuller
