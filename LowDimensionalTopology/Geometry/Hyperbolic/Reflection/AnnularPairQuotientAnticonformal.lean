module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCayleyOrbitTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularDiscGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFirstMirrorCayleyFormula
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.External.LiZhongQC.Ch09.S31_FiniteType
public import Mathlib.Analysis.Calculus.Deriv.Star

/-! The original first-mirror involution is anticonformal on its actual
Cayley Mobius quotient with the existing quotient atlas. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

/-- The accepted native first-mirror map on the same original Cayley orbit quotient. -/
def annularPairDiscQuotientReflection
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    MobiusDomainQuotient P.cayleyData.domain ≃ₜ MobiusDomainQuotient P.cayleyData.domain :=
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  Φ.symm.trans
    ((annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr).trans Φ)

/-- Its actual projection square is the original first mirror, not an independently chosen map. -/
theorem annularPairDiscQuotientReflection_projection
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) (z : ℍ) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    annularPairDiscQuotientReflection E r x hE hr hin hout
        (mobiusDomainProjection P.cayleyData.domain (P.cayleyCoordinate z)) =
      mobiusDomainProjection P.cayleyData.domain
        (P.cayleyCoordinate
          ((annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0).reflection z)) := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  change Φ (J (Φ.symm (mobiusDomainProjection P.cayleyData.domain (P.cayleyCoordinate z)))) = _
  rw [← annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z,
    Φ.symm_apply_apply, annularPairQuotientReflection_projection,
    annularPairCayleyOrbitHomeomorph_projection]

theorem annularPairDiscQuotientReflection_involutive
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    Function.Involutive (annularPairDiscQuotientReflection E r x hE hr hin hout) := by
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  let J := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  intro q
  change Φ (J (Φ.symm (Φ (J (Φ.symm q))))) = q
  rw [Φ.symm_apply_apply,
    annularPairQuotientReflection_involutive E r x (zero_lt_one.trans hE) hr,
    Φ.apply_symm_apply]

/-- The SAME actual quotient reflection is anticonformal in any two genuine
charts of its existing quotient atlas, over their entire actual map domain. -/
theorem annularPairDiscQuotientReflection_conj_differentiableOn_chart
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let Rq := mobiusQuotientRiemannSurface P.cayleyData.domain P.cayleyData.discontinuous
    ∀ b ∈ Rq.charts, ∀ d ∈ Rq.charts,
      DifferentiableOn ℂ
        (fun z => starRingEnd ℂ (riemannChartMap b
          (annularPairDiscQuotientReflection E r x hE hr hin hout) d z))
        (riemannChartMapDomain b
          (annularPairDiscQuotientReflection E r x hE hr hin hout) d) := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let D := P.cayleyData.domain
  let Rq := mobiusQuotientRiemannSurface D P.cayleyData.discontinuous
  let B := Rq.toRiemannAtlas
  let J := annularPairDiscQuotientReflection E r x hE hr hin hout
  let π := mobiusDomainProjection D
  let C := P.cayleyCoordinate
  let σ := (halfPlaneLineReflectionIsometry
    (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0)).toHomeomorph
  let μ := C.symm.trans (σ.trans C)
  let e := discFiniteChart
  have heAll (u : D.carrier) : u ∈ e.source := by
    change u ∈ discFiniteChart.source
    rw [discFiniteChart_source]
    trivial
  have hcomm (u : D.carrier) : J (π u) = π (μ u) := by
    obtain ⟨z, rfl⟩ := C.surjective u
    change J (π (C z)) = π (C (σ (C.symm (C z))))
    rw [C.symm_apply_apply]
    exact annularPairDiscQuotientReflection_projection E r x hE hr hin hout z
  have hfinite (z : ℍ) : e (C z) = (halfPlaneToDisc z : ℂ) := by
    exact congrArg (fun u : Complex.UnitDisc => (u : ℂ)) (P.cayleyCoordinate_finite z)
  have hμ (u : D.carrier) : e (μ u) = -starRingEnd ℂ (e u) := by
    obtain ⟨z, rfl⟩ := C.surjective u
    change e (C (σ (C.symm (C z)))) = -starRingEnd ℂ (e (C z))
    rw [C.symm_apply_apply, hfinite, hfinite]
    exact congrArg (fun u : Complex.UnitDisc => (u : ℂ))
      (halfPlaneToDisc_annularPairFirstMirror E r x (zero_lt_one.trans hE) hr z)
  -- All covering hypotheses concern this exact Cayley group and this exact projection.
  have hcover := mobiusDomain_noElliptic_covering D P.cayleyData.discontinuous
    (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
  have hpl : IsLocalHomeomorph π := hcover.isCoveringMap.isLocalHomeomorph
  have hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B π :=
    mobiusDomainProjection_analytic D P.cayleyData.discontinuous
  change ∀ b ∈ B.charts, ∀ d ∈ B.charts,
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (riemannChartMap b J d z))
      (riemannChartMapDomain b J d)
  intro b hb d hd z hz
  change z ∈ b.target ∧ J (b.symm z) ∈ d.source at hz
  obtain ⟨u, hu⟩ := mobiusDomainProjection_surjective D (b.symm z)
  change π u = b.symm z at hu
  have hbu : π u ∈ b.source := by
    rw [hu]
    exact b.map_target hz.1
  have hdu : J (π u) ∈ d.source := by
    rw [hu]
    exact hz.2
  obtain ⟨l, hul, hl⟩ := hpl u
  let F := e.symm.trans (l.trans b)
  have hsub : F.source ⊆ riemannChartMapDomain e π b := by
    intro w hw
    change w ∈ e.target ∧ e.symm w ∈ l.source ∧ l (e.symm w) ∈ b.source at hw
    refine ⟨hw.1, ?_⟩
    change π (e.symm w) ∈ b.source
    rw [hl]
    exact hw.2.2
  have hF : AnalyticOnNhd ℂ F F.source := by
    apply AnalyticOnNhd.congr F.open_source
      ((hpa.2 e discFiniteChart_mem b hb).mono hsub)
    intro w _
    change b (π (e.symm w)) = b (l (e.symm w))
    rw [hl]
  have hFu : e u ∈ F.source := by
    change e u ∈ e.target ∧ e.symm (e u) ∈ l.source ∧
      l (e.symm (e u)) ∈ b.source
    rw [e.left_inv (heAll u), ← hl]
    exact ⟨e.map_source (heAll u), hul, hbu⟩
  have hFz : F (e u) = z := by
    change b (l (e.symm (e u))) = z
    rw [e.left_inv (heAll u), ← hl, hu]
    exact b.right_inv hz.1
  have hzt : z ∈ F.target := hFz ▸ F.map_source hFu
  have hFi : F.symm z = e u := by
    rw [← hFz, F.left_inv hFu]
  have hi : AnalyticAt ℂ F.symm z := openPartialHomeomorph_analytic_inverse F hF z hzt
  let G := riemannChartMap e π d
  have hG : DifferentiableAt ℂ G (e (μ u)) := by
    apply (hpa.2 e discFiniteChart_mem d hd
      (e (μ u)) ?_).differentiableAt
    refine riemannChartMapDomain_mem e π d (μ u) (heAll (μ u)) ?_
    rw [← hcomm u]
    exact hdu
  have hGn : DifferentiableAt ℂ G (-starRingEnd ℂ (e u)) := by
    rw [← hμ u]
    exact hG
  have hneg : DifferentiableAt ℂ (fun t : ℂ => G (-t)) (starRingEnd ℂ (e u)) :=
    hGn.comp _ differentiableAt_id.neg
  let K : ℂ → ℂ := fun t => starRingEnd ℂ (G (-starRingEnd ℂ t))
  have hK : DifferentiableAt ℂ K (e u) := by
    simpa [K, Function.comp_def] using hneg.conj_conj
  have hKFi : DifferentiableAt ℂ K (F.symm z) := by
    rw [hFi]
    exact hK
  have hc : DifferentiableAt ℂ (fun t => K (F.symm t)) z :=
    hKFi.comp z hi.differentiableAt
  have hEq : (fun t => K (F.symm t)) =ᶠ[𝓝 z]
      (fun t => starRingEnd ℂ (riemannChartMap b J d t)) := by
    filter_upwards [F.open_target.mem_nhds hzt] with t ht
    have hs : F.symm t ∈ F.source := F.map_target ht
    change F.symm t ∈ e.target ∧ e.symm (F.symm t) ∈ l.source ∧
      l (e.symm (F.symm t)) ∈ b.source at hs
    let a := e.symm (F.symm t)
    have hπa : π a = b.symm t := by
      rw [hl]
      have hh := congrArg b.symm (F.right_inv ht)
      change b.symm (b (l a)) = b.symm t at hh
      rw [b.left_inv hs.2.2] at hh
      exact hh
    have hea : e a = F.symm t := e.right_inv hs.1
    change starRingEnd ℂ (G (-starRingEnd ℂ (F.symm t))) =
      starRingEnd ℂ (d (J (b.symm t)))
    calc
      starRingEnd ℂ (G (-starRingEnd ℂ (F.symm t))) =
          starRingEnd ℂ (G (e (μ a))) := by rw [hμ a, hea]
      _ = starRingEnd ℂ (d (π (μ a))) := by
        change starRingEnd ℂ (d (π (e.symm (e (μ a))))) = _
        rw [e.left_inv (heAll (μ a))]
      _ = starRingEnd ℂ (d (J (π a))) := by rw [hcomm a]
      _ = starRingEnd ℂ (d (J (b.symm t))) := by rw [hπa]
  exact (hc.congr_of_eventuallyEq hEq.symm).differentiableWithinAt

/-- The same actual disc-quotient reflection is anticonformal in its existing quotient atlas. -/
theorem annularPairDiscQuotientReflection_anticonformal
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let Rq := mobiusQuotientRiemannSurface P.cayleyData.domain P.cayleyData.discontinuous
    letI := Rq.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsAnticonformalInvolution
      (annularPairDiscQuotientReflection E r x hE hr hin hout) := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let Rq := mobiusQuotientRiemannSurface P.cayleyData.domain P.cayleyData.discontinuous
  let := Rq.toRiemannAtlas.toChartedSpace
  let J := annularPairDiscQuotientReflection E r x hE hr hin hout
  change LiZhongQC.IsAnticonformalInvolution J
  refine ⟨annularPairDiscQuotientReflection_involutive E r x hE hr hin hout, ?_⟩
  intro q
  change DifferentiableOn ℂ
    (fun z => starRingEnd ℂ (riemannChartMap (chartAt ℂ q) J (chartAt ℂ (J q)) z))
    (riemannChartMapDomain (chartAt ℂ q) J (chartAt ℂ (J q)))
  exact annularPairDiscQuotientReflection_conj_differentiableOn_chart E r x hE hr hin hout
    (chartAt ℂ q) (chart_mem_atlas ℂ q) (chartAt ℂ (J q)) (chart_mem_atlas ℂ (J q))

end LowDimensionalTopology.Geometry.Hyperbolic
