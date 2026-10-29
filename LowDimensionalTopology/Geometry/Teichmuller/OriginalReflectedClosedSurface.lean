module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedAtlasTransport
public import LowDimensionalTopology.External.LiZhongQC.Ch09.S31_FiniteType
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugate charts on the same original closed surface

The carrier, topology and point map are unchanged. The explicit preferred
charts are conjugated before the existing native-atlas adapter is used.
No existence of an antiholomorphic involution is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces

/-- Conjugate a genuine complex chart on its unchanged source. -/
def originalReflectedChart {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) : OpenPartialHomeomorph X ℂ where
  toFun := fun x => conj (e x)
  invFun := fun z => e.symm (conj z)
  source := e.source
  target := conj ⁻¹' e.target
  map_source' := by
    intro x hx
    simpa only [mem_preimage, Complex.conj_conj] using e.map_source hx
  map_target' := by
    intro z hz
    exact e.map_target hz
  left_inv' := by
    intro x hx
    simpa only [Complex.conj_conj] using e.left_inv hx
  right_inv' := by
    intro z hz
    simpa only [Complex.conj_conj] using congrArg conj (e.right_inv hz)
  continuousOn_toFun := Complex.continuous_conj.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.continuousOn_symm.comp
    Complex.continuous_conj.continuousOn (fun _ hz => hz)
  open_source := e.open_source
  open_target := e.open_target.preimage Complex.continuous_conj

/-- The actual conjugate chart has the original point domain. -/
@[simp] theorem originalReflectedChart_source {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) : (originalReflectedChart e).source = e.source := rfl

/-- Its coordinate range is the conjugate of the original range. -/
@[simp] theorem originalReflectedChart_target {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) :
    (originalReflectedChart e).target = conj ⁻¹' e.target := rfl

/-- The forward chart is literal complex conjugation after the old chart. -/
@[simp] theorem originalReflectedChart_apply {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) :
    originalReflectedChart e x = conj (e x) := rfl

/-- The inverse chart applies the old inverse to the conjugated coordinate. -/
@[simp] theorem originalReflectedChart_symm_apply {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    (originalReflectedChart e).symm z = e.symm (conj z) := rfl

/-- The complete original complex chart set, conjugated on the same surface. -/
def originalMirrorAtlas (S : LiZhongQC.ClosedRS.{0}) : RiemannAtlas S.carrier where
  charts := originalReflectedChart '' atlas ℂ S.carrier
  cover x := ⟨originalReflectedChart (chartAt ℂ x),
    mem_image_of_mem _ (chart_mem_atlas ℂ x), mem_chart_source ℂ x⟩
  compatible := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    let A := RiemannAtlas.ofManifold S.carrier
    have hsource : ((originalReflectedChart e).symm.trans
        (originalReflectedChart f)).source = conj ⁻¹' (e.symm.trans f).source := rfl
    have hdiff : DifferentiableOn ℂ
        ((originalReflectedChart e).symm.trans (originalReflectedChart f))
        ((originalReflectedChart e).symm.trans (originalReflectedChart f)).source := by
      intro z hz
      have hzold : conj z ∈ (e.symm.trans f).source := by
        rwa [hsource] at hz
      have hd := (@AnalyticAt.differentiableAt ℂ _ ℂ _
        NormedField.toNormedSpace ℂ _ NormedField.toNormedSpace
        _ _ (A.compatible e he f hf (conj z) hzold)).conj_conj
      have hd' : DifferentiableAt ℂ
          ((originalReflectedChart e).symm.trans (originalReflectedChart f)) z := by
        simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_def,
          originalReflectedChart_apply, originalReflectedChart_symm_apply,
          Complex.conj_conj] using hd
      exact hd'.differentiableWithinAt
    exact hdiff.analyticOnNhd
      ((originalReflectedChart e).symm.trans (originalReflectedChart f)).open_source

/-- Explicit preferred reflected charts, before any native choice of charts. -/
@[instance_reducible] def originalMirrorChartedSpace (S : LiZhongQC.ClosedRS.{0}) : ChartedSpace ℂ S.carrier where
  atlas := (originalMirrorAtlas S).charts
  chartAt x := originalReflectedChart (chartAt ℂ x)
  mem_chart_source x := mem_chart_source ℂ x
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas ℂ x)

/-- The actual reflected overlap maps form an analytic manifold. -/
theorem originalMirror_isManifold (S : LiZhongQC.ClosedRS.{0}) :
    letI := originalMirrorChartedSpace S
    IsManifold 𝓘(ℂ) ω S.carrier := by
  let := originalMirrorChartedSpace S
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω S.carrier
  intro e f he hf
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id,
    Set.inter_univ] using
    ((originalMirrorAtlas S).compatible e he f hf).contDiffOn (n := ω)
      (e.symm.trans f).open_source.uniqueDiffOn

/-- The mirror closed surface has exactly the original carrier and topology. -/
def originalMirrorClosedRS (S : LiZhongQC.ClosedRS.{0}) : LiZhongQC.ClosedRS.{0} where
  carrier := S.carrier
  topologicalSpace := S.topologicalSpace
  t2Space := S.t2Space
  connectedSpace := S.connectedSpace
  compactSpace := S.compactSpace
  chartedSpace := originalMirrorChartedSpace S
  isManifold := originalMirror_isManifold S

/-- The same reflected surface read in the existing native atlas language. -/
def originalMirrorNative (S : LiZhongQC.ClosedRS.{0}) : ClosedRiemannSurface S.carrier :=
  (originalMirrorClosedRS S).toNative

/-- The canonical mirror map is the identity on the original point set. -/
def originalMirrorCanonicalMap (S : LiZhongQC.ClosedRS.{0}) :
    S.carrier ≃ₜ (originalMirrorClosedRS S).carrier := Homeomorph.refl _

/-- In the two actual atlases, conjugating the canonical local expression is holomorphic. -/
theorem originalMirrorCanonicalMap_antiholomorphic (S : LiZhongQC.ClosedRS.{0}) :
    ∀ x : S.carrier, DifferentiableOn ℂ
      (fun z => conj (@LiZhongQC.localMapExpr S.carrier S.topologicalSpace S.chartedSpace
        S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
        (originalMirrorCanonicalMap S) x z))
      (@LiZhongQC.localMapDomain S.carrier S.topologicalSpace S.chartedSpace
        S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
        (originalMirrorCanonicalMap S) x) := by
  intro x
  apply differentiableOn_id.congr
  intro z hz
  change conj (conj (S.chartedSpace.chartAt x ((S.chartedSpace.chartAt x).symm z))) = z
  rw [Complex.conj_conj]
  exact (S.chartedSpace.chartAt x).right_inv hz.1

/-- Double conjugation preserves the QC constant of the same actual map. -/
theorem originalMirror_isKQCRS (S T : LiZhongQC.ClosedRS.{0})
    (f : S.carrier ≃ₜ T.carrier) (K : ℝ)
    (hf : @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f K) :
    @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f K := by
  refine ⟨hf.1, fun x => ?_⟩
  have hexpr : @LiZhongQC.localMapExpr S.carrier S.topologicalSpace
      (originalMirrorChartedSpace S) T.carrier T.topologicalSpace
      (originalMirrorChartedSpace T) f x =
        fun z => conj (@LiZhongQC.localMapExpr S.carrier S.topologicalSpace
          S.chartedSpace T.carrier T.topologicalSpace T.chartedSpace f x (conj z)) := rfl
  have hdomain : @LiZhongQC.localMapDomain S.carrier S.topologicalSpace
      (originalMirrorChartedSpace S) T.carrier T.topologicalSpace
      (originalMirrorChartedSpace T) f x =
        conj ⁻¹' @LiZhongQC.localMapDomain S.carrier S.topologicalSpace
          S.chartedSpace T.carrier T.topologicalSpace T.chartedSpace f x := rfl
  rw [hexpr, hdomain]
  exact LiZhongQC.abR_x_isKQC_conj (hf.2 x)

/-- The original QC homeomorphism remains QC between the two mirrors. -/
theorem originalMirror_isQCRS (S T : LiZhongQC.ClosedRS.{0})
    (f : S.carrier ≃ₜ T.carrier)
    (hf : @LiZhongQC.IsQCRS S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace f) :
    @LiZhongQC.IsQCRS S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      T.carrier T.topologicalSpace (originalMirrorChartedSpace T) f := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K, originalMirror_isKQCRS S T f K hK⟩

/-- A given original antiholomorphic involution is conformal into its mirror. -/
theorem originalInvolution_isKQCRS_toMirror (S : LiZhongQC.ClosedRS.{0})
    (J : S.carrier ≃ₜ S.carrier)
    (hJ : @LiZhongQC.IsAnticonformalInvolution S.carrier S.topologicalSpace
      S.chartedSpace J) :
    @LiZhongQC.IsKQCRS S.carrier S.topologicalSpace S.chartedSpace
      S.carrier S.topologicalSpace (originalMirrorChartedSpace S) J 1 := by
  refine ⟨le_rfl, fun x => ?_⟩
  change LiZhongQC.IsKQC
    (fun z => conj (@LiZhongQC.localMapExpr S.carrier S.topologicalSpace
      S.chartedSpace S.carrier S.topologicalSpace S.chartedSpace J x z))
    (@LiZhongQC.localMapDomain S.carrier S.topologicalSpace S.chartedSpace
      S.carrier S.topologicalSpace S.chartedSpace J x) 1
  apply LiZhongQC.isKQC_one_of_conformal
    (@LiZhongQC.s23_localMapDomain_isOpen S.carrier S.topologicalSpace
      S.chartedSpace S.carrier S.topologicalSpace S.chartedSpace J J.continuous x)
  refine ⟨hJ.2 x, ?_, rfl⟩
  intro z hz w hw heq
  apply (@LiZhongQC.s23_c1_injOn_localMapExpr S.carrier S.topologicalSpace
    S.chartedSpace S.carrier S.topologicalSpace S.chartedSpace J J.injective x) hz hw
  simpa only [Complex.conj_conj] using congrArg conj heq

/-- A conformal original target map is conformal between the same mirrors. -/
theorem originalMirror_isBiholomorphic (S T : LiZhongQC.ClosedRS.{0})
    (c : S.carrier ≃ₜ T.carrier)
    (hc : @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace c) :
    @LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace
      (originalMirrorChartedSpace S) T.carrier T.topologicalSpace
      (originalMirrorChartedSpace T) c := by
  apply (@LiZhongQC.isKQCRS_one_iff S.carrier S.topologicalSpace
    (originalMirrorChartedSpace S) T.carrier T.topologicalSpace
    (originalMirrorChartedSpace T) (originalMirror_isManifold S)
    (originalMirror_isManifold T) c).mp
  exact originalMirror_isKQCRS S T c 1
    ((@LiZhongQC.isKQCRS_one_iff S.carrier S.topologicalSpace S.chartedSpace
      T.carrier T.topologicalSpace T.chartedSpace S.isManifold T.isManifold c).mpr hc)

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
