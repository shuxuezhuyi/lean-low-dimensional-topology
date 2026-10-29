module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairDiscCoreReflection
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Covering

/-! The same original core reflection is anticonformal in its actual
inherited open-subset complex atlas. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

/-- The already defined reflection on the original open Nielsen core is
anticonformal in the actual inherited open-subset complex atlas. -/
theorem annularPairDiscCoreReflection_anticonformal
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let C := threeBoundaryOpenCore P.cayleyData hNE
    let Rq := mobiusQuotientRiemannSurface P.cayleyData.domain P.cayleyData.discontinuous
    let Ac := Rq.toRiemannAtlas.liftLocalHomeomorph
      (Subtype.val : C → MobiusDomainQuotient P.cayleyData.domain)
      (isOpen_threeBoundaryOpenCore P.cayleyData hNE).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    letI := Ac.toChartedSpace
    LiZhongQC.IsAnticonformalInvolution
      (annularPairDiscCoreReflection E r x hE hr hin hout) := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let Q := MobiusDomainQuotient P.cayleyData.domain
  let Rq := mobiusQuotientRiemannSurface P.cayleyData.domain P.cayleyData.discontinuous
  let A := Rq.toRiemannAtlas
  let C := threeBoundaryOpenCore P.cayleyData hNE
  have hC : IsOpen C := isOpen_threeBoundaryOpenCore P.cayleyData hNE
  let i : C → Q := Subtype.val
  let Ac := A.liftLocalHomeomorph i hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  let := Ac.toChartedSpace
  let Jd := annularPairDiscQuotientReflection E r x hE hr hin hout
  let j := annularPairDiscCoreReflection E r x hE hr hin hout
  have hproj (q : C) : i (j q) = Jd (i q) := rfl
  change LiZhongQC.IsAnticonformalInvolution j
  refine ⟨?_, ?_⟩
  · intro q
    apply Subtype.ext
    change Jd (Jd q.val) = q.val
    exact annularPairDiscQuotientReflection_involutive E r x hE hr hin hout q.val
  · intro q
    have he : chartAt ℂ q ∈ coveringLiftedCharts A i := chart_mem_atlas ℂ q
    have hf : chartAt ℂ (j q) ∈ coveringLiftedCharts A i := chart_mem_atlas ℂ (j q)
    obtain ⟨l, hl, b, hb, he⟩ := he
    obtain ⟨m, hm, d, hd, hf⟩ := hf
    change DifferentiableOn ℂ
      (fun z => starRingEnd ℂ (riemannChartMap (chartAt ℂ q) j (chartAt ℂ (j q)) z))
      (riemannChartMapDomain (chartAt ℂ q) j (chartAt ℂ (j q)))
    rw [he, hf]
    have hsub : riemannChartMapDomain (l.trans b) j (m.trans d) ⊆
        riemannChartMapDomain b Jd d := by
      intro z hz
      have hp := coveringLiftedChart_project_symm i l hl b z hz.1
      refine ⟨hz.1.1, ?_⟩
      change Jd (b.symm z) ∈ d.source
      rw [← hp, ← hproj, hm]
      exact hz.2.2
    apply DifferentiableOn.congr
      ((annularPairDiscQuotientReflection_conj_differentiableOn_chart
        E r x hE hr hin hout b hb d hd).mono hsub)
    intro z hz
    change starRingEnd ℂ (d (m (j ((l.trans b).symm z)))) =
      starRingEnd ℂ (d (Jd (b.symm z)))
    rw [← hm, hproj, coveringLiftedChart_project_symm i l hl b z hz.1]

end LowDimensionalTopology.Geometry.Hyperbolic
