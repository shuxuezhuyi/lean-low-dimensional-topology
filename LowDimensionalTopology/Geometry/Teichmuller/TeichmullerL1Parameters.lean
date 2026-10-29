module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1Norm
public import LowDimensionalTopology.Geometry.Teichmuller.RadialNormBall
public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCParameterHomeomorph
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The actual L1 Teichmüller parameter map

The parameter is the original-atlas quadratic differential itself, with norm
`2 ∫ |q|`. Its deformation stretch is exactly this book norm. Euclidean
coordinates enter only the proof of continuity and bijectivity: positive-ray
rescaling and uniqueness identify that proof with the same actual parameter map.
The target has the explicit full-log QC metric on native marked classes.

The analytic theorems come from Wu Xiaobin's Li-Zhong-QC-formalization at
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter Metric Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem exists_l1Deformation
    (q : ↥(QuadraticL1.openUnitBall R)) (hq : q.val ≠ 0) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ p : LiZhongQC.TeichSpace X,
      LiZhongQC.IsDeformationPoint (q.val : X → ℂ → ℂ)
        (QuadraticL1.bookNorm R q.val) p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hq' : (q.val : X → ℂ → ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  have hk0 : 0 ≤ QuadraticL1.bookNorm R q.val := by
    unfold QuadraticL1.bookNorm
    positivity
  have hk1 := (QuadraticL1.mem_openUnitBall R q.val).mp q.property
  obtain ⟨S, f, q', hT⟩ := LiZhongQC.exists_teichDeformation q.val.property hq' hk0 hk1
  let hqc := (LiZhongQC.teichDeformation_isTeichmullerMap hT).qc
  exact ⟨Quot.mk _ ⟨S, f, hqc⟩, S, f, hqc, q', hT, rfl⟩

private def sourceL1ParameterMap (q : ↥(QuadraticL1.openUnitBall R)) :
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.TeichSpace X := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  exact if hq : q.val = 0 then TeichmullerSpace.toSource R (TeichmullerSpace.basePoint R)
    else Classical.choose (exists_l1Deformation R q hq)

private theorem sourceL1ParameterMap_zero (q : ↥(QuadraticL1.openUnitBall R))
    (hq : q.val = 0) :
    let := R.toRiemannAtlas.toChartedSpace
    sourceL1ParameterMap R q = TeichmullerSpace.toSource R (TeichmullerSpace.basePoint R) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  simp only [sourceL1ParameterMap, dite_eq_left hq]

private theorem sourceL1ParameterMap_deformation (q : ↥(QuadraticL1.openUnitBall R))
    (hq : q.val ≠ 0) :
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsDeformationPoint (q.val : X → ℂ → ℂ)
      (QuadraticL1.bookNorm R q.val) (sourceL1ParameterMap R q) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  simpa only [sourceL1ParameterMap, dite_eq_right hq] using
    Classical.choose_spec (exists_l1Deformation R q hq)

namespace TeichmullerSpace

/-- The book parameter map: deform using the actual initial differential `q` and
stretch `2 ∫ |q|`, then use the actual equivalence of native and QC-marked classes. -/
@[no_expose]
def l1ParameterMap {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (q : ↥(QuadraticL1.openUnitBall R)) : TeichmullerSpace.{u, u} R := by
  let := R.toRiemannAtlas.toChartedSpace
  exact (qcEquiv R hg hgenus).symm (sourceL1ParameterMap R q)

/-- Zero is sent to the original identity-marked complex structure. -/
theorem l1ParameterMap_zero {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (q : ↥(QuadraticL1.openUnitBall R)) (hq : q.val = 0) :
    l1ParameterMap R hg hgenus q = basePoint R := by
  let := R.toRiemannAtlas.toChartedSpace
  apply (qcEquiv R hg hgenus).injective
  change (qcEquiv R hg hgenus)
    ((qcEquiv R hg hgenus).symm (sourceL1ParameterMap R q)) = toSource R (basePoint R)
  exact ((qcEquiv R hg hgenus).apply_symm_apply _).trans
    (sourceL1ParameterMap_zero R q hq)

/-- At every nonzero parameter, the initial differential is literally `q`, and the
stretch is the precise book L1 norm on its original complex atlas. -/
theorem l1ParameterMap_deformation {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (q : ↥(QuadraticL1.openUnitBall R)) (hq : q.val ≠ 0) :
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsDeformationPoint (q.val : X → ℂ → ℂ)
      (QuadraticL1.bookNorm R q.val) (toSource R (l1ParameterMap R hg hgenus q)) := by
  let := R.toRiemannAtlas.toChartedSpace
  change LiZhongQC.IsDeformationPoint _ _ ((qcEquiv R hg hgenus)
    ((qcEquiv R hg hgenus).symm (sourceL1ParameterMap R q)))
  rw [Equiv.apply_symm_apply]
  exact sourceL1ParameterMap_deformation R q hq

/-- The same actual book-L1 parameter map is a surjective homeomorphism onto the
native marked quotient equipped with its actual full-log QC metric. -/
theorem l1ParameterMap_homeomorphism {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
    let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
      mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let mT : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    IsHomeomorph (l1ParameterMap R hg hgenus) ∧
      Nonempty (TeichmullerSpace.{u, u} R ≃ₜ EuclideanSpace ℝ (Fin (6 * g - 6))) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let Q := HolomorphicQuadraticDifferential R.toRiemannAtlas
  let G := QuadraticL1.normedAddCommGroup R
  let : NormedAddCommGroup Q := G
  let : MetricSpace Q := G.toMetricSpace
  let : UniformSpace Q := G.toMetricSpace.toUniformSpace
  let : TopologicalSpace Q := G.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ Q := QuadraticL1.normedSpace R
  let : NormedSpace ℝ Q := NormedSpace.restrictScalars ℝ ℂ Q
  let mQ : MetricSpace ↥(QuadraticL1.openUnitBall R) := QuadraticL1.unitBallMetricSpace R
  let : TopologicalSpace ↥(QuadraticL1.openUnitBall R) :=
    mQ.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let mT : MetricSpace (TeichmullerSpace.{u, u} R) := qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hX := R.hasSourceGenus hgenus
  let : MetricSpace (LiZhongQC.TeichSpace X) := QCBookMetric.metricSpace hg hX
  obtain ⟨_, e, _⟩ := LiZhongQC.teichDeformationSpace_parameters hg hX
  let er : Q ≃ₗ[ℝ] (LiZhongQC.holQuadDiffSubmodule X).restrictScalars ℝ :=
    ((Submodule.restrictScalarsEquiv ℝ ℂ (X → ℂ → ℂ)
      (LiZhongQC.holQuadDiffSubmodule X)).restrictScalars ℝ).symm
  let en := er.trans e
  let : FiniteDimensional ℝ Q := en.symm.finiteDimensional
  let enc : Q ≃L[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)) := en.toContinuousLinearEquiv
  let A : ↥(QuadraticL1.openUnitBall R) ≃ₜ
      ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1) :=
    radialUnitBallHomeomorph enc
  obtain ⟨B, hB, hBzero⟩ := sourceCoordinateHomeomorph hg hX e
  let I : TeichmullerSpace.{u, u} R ≃ᵢ LiZhongQC.TeichSpace X :=
    { toEquiv := qcEquiv R hg hgenus
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  let H := A.trans (B.trans I.symm.toHomeomorph)
  have hsame : (H : ↥(QuadraticL1.openUnitBall R) → TeichmullerSpace.{u, u} R) =
      l1ParameterMap R hg hgenus := by
    funext q
    apply (qcEquiv R hg hgenus).injective
    change (qcEquiv R hg hgenus) ((qcEquiv R hg hgenus).symm (B (A q))) =
      (qcEquiv R hg hgenus) ((qcEquiv R hg hgenus).symm (sourceL1ParameterMap R q))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    by_cases hq : q.val = 0
    · have hAzero : ((A q : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1)) :
          EuclideanSpace ℝ (Fin (6 * g - 6))) = 0 := by
        change radialNormMap enc q.val = 0
        rw [hq, radialNormMap_zero]
      exact (hBzero (A q) hAzero).trans (sourceL1ParameterMap_zero R q hq).symm
    · obtain ⟨q₀, _, hdef, hdir⟩ := hB (A q)
      have hnorm : ‖((A q : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1)) :
          EuclideanSpace ℝ (Fin (6 * g - 6)))‖ = ‖q.val‖ :=
        norm_radialNormMap enc q.val
      have hv : ((A q : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1)) :
          EuclideanSpace ℝ (Fin (6 * g - 6))) ≠ 0 := by
        intro h
        have hn := congrArg norm h
        rw [hnorm, norm_zero] at hn
        exact hq (norm_eq_zero.mp hn)
      have hn : ‖en q.val‖ ≠ 0 := norm_ne_zero_iff.mpr
        (fun h => hq (en.injective (h.trans en.map_zero.symm)))
      have hqpos : 0 < ‖q.val‖ := norm_pos_iff.mpr hq
      have hfactor : 0 < ‖q.val‖ / ‖en q.val‖ :=
        div_pos hqpos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn))
      have hrel : ‖q.val‖ • e q₀ = (‖q.val‖ / ‖en q.val‖) • en q.val := by
        have hdirection := hdir hv
        rw [hnorm] at hdirection
        change ‖q.val‖ • e q₀ = radialNormMap enc q.val at hdirection
        exact hdirection
      have hcancel : (‖q.val‖ / ‖en q.val‖) • (‖en q.val‖ • e q₀) =
          (‖q.val‖ / ‖en q.val‖) • en q.val := by
        rw [smul_smul, div_mul_cancel₀ _ hn]
        exact hrel
      have hq₀ : (‖en q.val‖ : ℝ) • q₀ = er q.val := by
        apply e.injective
        rw [map_smul]
        exact smul_right_injective _ hfactor.ne' hcancel
      have hfun : ((‖en q.val‖ : ℝ) : ℂ) • (q₀ : X → ℂ → ℂ) =
          (q.val : X → ℂ → ℂ) := by
        funext x z
        have hh := congrArg (fun r : (LiZhongQC.holQuadDiffSubmodule X).restrictScalars ℝ =>
          (r : X → ℂ → ℂ) x z) hq₀
        change (‖en q.val‖ : ℂ) * (q₀ : X → ℂ → ℂ) x z = _
        change (‖en q.val‖ : ℝ) • (q₀ : X → ℂ → ℂ) x z =
          (q.val : X → ℂ → ℂ) x z at hh
        simpa only [Complex.real_smul] using hh
      have hscaled := LiZhongQC.utm_x_isDeformationPoint_smul hdef
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn))
      rw [hfun, hnorm, QuadraticL1.norm_eq_bookNorm R q.val] at hscaled
      exact LiZhongQC.isDeformationPoint_unique hg hX hscaled
        (sourceL1ParameterMap_deformation R q hq)
  refine ⟨hsame ▸ H.isHomeomorph, ?_⟩
  exact ⟨H.symm.trans (A.trans (Homeomorph.unitBall
    (E := EuclideanSpace ℝ (Fin (6 * g - 6)))).symm)⟩

end TeichmullerSpace
end LowDimensionalTopology.Geometry.Teichmuller
