module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiComposition
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiBanach
public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import LowDimensionalTopology.External.LiZhongQC.Ch05.S21_UniversalTeichmuller

/-!
# Quantitative local control for the native Beltrami projection

An explicit uniform coefficient bound gives the corresponding explicit QC
constant on the original surface atlases. The accompanying Banach estimate
controls the actual phase-bearing relative-coefficient expression. These
statements give continuity of the actual realized-coefficient projection into the
explicit QC metric topology, without identifying the reverse quotient topology.
-/

@[expose] public section
noncomputable section

open Set
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

universe u v

namespace SmoothSurfaceEquiv

/-- Retain the prescribed coefficient bound in the resulting actual QC constant.
No compactness or finite-area hypothesis is needed when the bound is supplied. -/
theorem isKQCRS_of_coeff_bound
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hk : ∀ (e : BeltramiDifferential.Chart R.toRiemannAtlas) (z : e.val.target),
      ‖(f.beltrami hf).coeff e z‖ ≤ k) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsKQCRS f.toHomeomorph ((1 + k) / (1 - k)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  refine ⟨?_, fun x => ?_⟩
  · rw [le_div_iff₀ (by linarith : 0 < 1 - k)]
    linarith
  · let e := chartAt ℂ x
    let g := chartAt ℂ (f.toHomeomorph x)
    have he : e ∈ R.charts := chart_mem_atlas ℂ x
    have hg : g ∈ S.charts := chart_mem_atlas ℂ (f.toHomeomorph x)
    let F := riemannHomeomorphChart e f.toHomeomorph g
    have hhomeo : LiZhongQC.IsHomeomorphOnto
        (riemannChartMap e f.toHomeomorph g)
        (riemannChartMapDomain e f.toHomeomorph g)
        ((riemannChartMap e f.toHomeomorph g) ''
          riemannChartMapDomain e f.toHomeomorph g) := by
      have h := LiZhongQC.isHomeomorphOnto_openPartialHomeomorph F
      change LiZhongQC.IsHomeomorphOnto
        (riemannChartMap e f.toHomeomorph g) F.source
        ((riemannChartMap e f.toHomeomorph g) '' F.source) at h
      rwa [show F.source = riemannChartMapDomain e f.toHomeomorph g from
        riemannHomeomorphChart_source e f.toHomeomorph g] at h
    have hC1 := f.chartMap_contDiffOn_real e he g hg
    change LiZhongQC.IsKQC (riemannChartMap e f.toHomeomorph g)
      (riemannChartMapDomain e f.toHomeomorph g) ((1 + k) / (1 - k))
    apply LiZhongQC.isKQC_of_contDiffOn_jacobian_pos_bound
      (riemannChartMapDomain_isOpen e f.toHomeomorph g f.toHomeomorph.continuous)
      hC1 hhomeo _ hk0 hk1
    · intro z hz
      have h := hk ⟨e, he⟩ ⟨z, hz.1⟩
      rwa [f.beltrami_coeff_eq_chartDilatation hf
        ⟨e, he⟩ ⟨z, hz.1⟩ g hg hz.2] at h
    · intro z hz
      have hpos := hf e he g hg z hz
      have hd : DifferentiableAt ℝ (riemannChartMap e f.toHomeomorph g) z :=
        (hC1.differentiableOn one_ne_zero).differentiableAt
          ((riemannChartMapDomain_isOpen e f.toHomeomorph g
            f.toHomeomorph.continuous).mem_nhds hz)
      change 0 < LinearMap.det
        (fderiv ℝ (riemannChartMap e f.toHomeomorph g) z : ℂ →ₗ[ℝ] ℂ) at hpos
      rwa [LiZhongQC.det_fderiv_eq_jacobian hd] at hpos

end SmoothSurfaceEquiv

namespace BeltramiDifferential

variable {X : Type u} [TopologicalSpace X] {A : RiemannAtlas X}

/-- The actual relative-coefficient expression is uniformly small when its
continuous tensor inputs are close in the native Banach norm. -/
theorem relative_fraction_norm_le
    (μ ν : BanachSpace A) (hμ : ‖μ‖ < 1) (hν : ‖ν‖ < 1)
    (e : Chart A) (z : e.val.target) {p : ℂ} (hp : p ≠ 0) :
    ‖(p / conj p) *
      (((toTensor ν).coeff e z - (toTensor μ).coeff e z) /
        (1 - conj ((toTensor μ).coeff e z) * (toTensor ν).coeff e z))‖ ≤
      ‖ν - μ‖ / (1 - ‖μ‖) := by
  let a := (toTensor μ).coeff e z
  let b := (toTensor ν).coeff e z
  have ha : ‖a‖ ≤ ‖μ‖ := μ.val.norm_coe_le_norm ⟨e, z⟩
  have hb : ‖b‖ < 1 := (ν.val.norm_coe_le_norm ⟨e, z⟩).trans_lt hν
  have hab : ‖conj a * b‖ ≤ ‖μ‖ := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖a‖ * ‖b‖ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left hb.le (norm_nonneg a)
      _ = ‖a‖ := mul_one _
      _ ≤ ‖μ‖ := ha
  have hden : 1 - ‖μ‖ ≤ ‖(1 : ℂ) - conj a * b‖ := by
    calc
      1 - ‖μ‖ ≤ 1 - ‖conj a * b‖ := sub_le_sub_left hab 1
      _ = ‖(1 : ℂ)‖ - ‖conj a * b‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - conj a * b‖ := norm_sub_norm_le _ _
  have hbasepos : 0 < 1 - ‖μ‖ := sub_pos.mpr hμ
  have hdenpos : 0 < ‖(1 : ℂ) - conj a * b‖ := hbasepos.trans_le hden
  have hnum : ‖b - a‖ ≤ ‖ν - μ‖ :=
    (ν - μ).val.norm_coe_le_norm ⟨e, z⟩
  have hphase : ‖p / conj p‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hp)]
  change ‖(p / conj p) * ((b - a) / (1 - conj a * b))‖ ≤ _
  rw [norm_mul, hphase, one_mul, norm_div]
  apply (div_le_div_iff₀ hdenpos hbasepos).2
  exact (mul_le_mul_of_nonneg_right hnum hbasepos.le).trans
    (mul_le_mul_of_nonneg_left hden (norm_nonneg (ν - μ)))

end BeltramiDifferential

namespace SmoothSurfaceEquiv

private theorem beltrami_congr
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    {f g : SmoothSurfaceEquiv R S} (hfg : f = g)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas g.toHomeomorph) :
    f.beltrami hf = g.beltrami hg := by
  cases hfg
  rfl

end SmoothSurfaceEquiv

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The actual relative smooth map between the two variable target surfaces. -/
def relativeSmooth (M N : MarkedRiemannSurface.{u, v} R) :
    SmoothSurfaceEquiv M.surface.toRiemannSurface N.surface.toRiemannSurface :=
  SmoothSurfaceEquiv.trans (SmoothSurfaceEquiv.symm M.marking) N.marking

theorem relativeSmooth_orientation (M N : MarkedRiemannSurface.{u, v} R) :
    PreservesComplexOrientation M.surface.toRiemannAtlas N.surface.toRiemannAtlas
      (relativeSmooth M N).toHomeomorph :=
  N.orientation_preserving.comp
    (PreservesComplexOrientation.homeomorph_symm
      M.marking.toHomeomorph M.orientation_preserving)
    M.marking.toHomeomorph.symm.continuous

theorem marking_trans_relativeSmooth (M N : MarkedRiemannSurface.{u, v} R) :
    SmoothSurfaceEquiv.trans M.marking (relativeSmooth M N) = N.marking := by
  let := R.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  apply Diffeomorph.ext
  intro x
  change N.marking.toHomeomorph
    (M.marking.toHomeomorph.symm (M.marking.toHomeomorph x)) = N.marking.toHomeomorph x
  rw [M.marking.toHomeomorph.symm_apply_apply]

/-- The coefficients of the actual relative map satisfy the uniform Banach estimate. -/
theorem relativeSmooth_coeff_norm_le (M N : MarkedRiemannSurface.{u, v} R)
    (b : BeltramiDifferential.Chart M.surface.toRiemannAtlas) (v : b.val.target) :
    ‖((relativeSmooth M N).beltrami (relativeSmooth_orientation M N)).coeff b v‖ ≤
      ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
        (1 - ‖M.beltramiCoefficient‖) := by
  let := R.compactSpace
  let h := relativeSmooth M N
  let hh := relativeSmooth_orientation M N
  let y := b.val.symm v.val
  let x := M.marking.toHomeomorph.symm y
  obtain ⟨a, ha, hxa⟩ := R.toRiemannAtlas.cover x
  obtain ⟨c, hc, hxc⟩ := N.surface.toRiemannAtlas.cover (N.marking.toHomeomorph x)
  let aa : BeltramiDifferential.Chart R.toRiemannAtlas := ⟨a, ha⟩
  let cc : BeltramiDifferential.Chart N.surface.toRiemannAtlas := ⟨c, hc⟩
  let zz : a.target := ⟨a x, a.map_source hxa⟩
  let F := riemannChartMap a M.marking.toHomeomorph b.val
  have hfx : M.marking.toHomeomorph x = y := M.marking.toHomeomorph.apply_symm_apply y
  have hyb : y ∈ b.val.source := b.val.map_target v.property
  have hy : M.marking.toHomeomorph (a.symm zz.val) ∈ b.val.source := by
    change M.marking.toHomeomorph (a.symm (a x)) ∈ b.val.source
    rw [a.left_inv hxa, hfx]
    exact hyb
  have hz : h.toHomeomorph (M.marking.toHomeomorph (a.symm zz.val)) ∈ c.source := by
    change N.marking.toHomeomorph
      (M.marking.toHomeomorph.symm (M.marking.toHomeomorph (a.symm (a x)))) ∈ c.source
    rw [M.marking.toHomeomorph.symm_apply_apply, a.left_inv hxa]
    exact hxc
  have hFv : F zz.val = v.val := by
    change b.val (M.marking.toHomeomorph (a.symm (a x))) = v.val
    rw [a.left_inv hxa, hfx]
    exact b.val.right_inv v.property
  have hq : (⟨F zz.val, b.val.map_source hy⟩ : b.val.target) = v :=
    Subtype.ext hFv
  have hcompTensor :
      (SmoothSurfaceEquiv.trans M.marking h).beltrami
          (hh.comp M.orientation_preserving M.marking.toHomeomorph.continuous) =
        N.beltramiTensor :=
    SmoothSurfaceEquiv.beltrami_congr (marking_trans_relativeSmooth M N)
      _ N.orientation_preserving
  have hsolve := (M.marking.beltrami_trans_solve_coeff h
    M.orientation_preserving hh aa b cc zz hy hz).2
  rw [hq, hcompTensor] at hsolve
  have hp : LiZhongQC.dz F zz.val ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg _)
      (M.marking.chartMap_wirtinger_lt M.orientation_preserving a ha
        b.val b.property ⟨zz.property, hy⟩))
  have hbound := BeltramiDifferential.relative_fraction_norm_le
    M.beltramiCoefficient N.beltramiCoefficient
    M.beltramiCoefficient_norm_lt_one N.beltramiCoefficient_norm_lt_one aa zz hp
  change ‖(h.beltrami hh).coeff b v‖ ≤ _
  rw [hsolve]
  simpa only [beltramiCoefficient, BeltramiDifferential.toTensor_ofTensor,
    beltramiTensor] using hbound

/-- A quantitative QC bound for the actual relative target homeomorphism. -/
theorem relativeSmooth_isKQCRS (M N : MarkedRiemannSurface.{u, v} R)
    (hd : ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
      (1 - ‖M.beltramiCoefficient‖) < 1) :
    letI := M.surface.toRiemannAtlas.toChartedSpace
    letI := N.surface.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsKQCRS (relativeSmooth M N).toHomeomorph
      ((1 + ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
          (1 - ‖M.beltramiCoefficient‖)) /
        (1 - ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
          (1 - ‖M.beltramiCoefficient‖))) := by
  exact (relativeSmooth M N).isKQCRS_of_coeff_bound (relativeSmooth_orientation M N)
    (div_nonneg (norm_nonneg _) (sub_pos.mpr M.beltramiCoefficient_norm_lt_one).le)
    hd (relativeSmooth_coeff_norm_le M N)

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The actual compatible relative map bounds the genuine full-log candidate infimum. -/
theorem fromQCDistance_mk_le_log_relative
    (M N : MarkedRiemannSurface.{u, u} R)
    (hd : ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
      (1 - ‖M.beltramiCoefficient‖) < 1) :
    fromQCDistance R (mk M) (mk N) ≤
      Real.log ((1 + ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
          (1 - ‖M.beltramiCoefficient‖)) /
        (1 - ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
          (1 - ‖M.beltramiCoefficient‖))) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  let := M.surface.connectedSpace
  let f := MarkedRiemannSurface.relativeSmooth M N
  let d := ‖N.beltramiCoefficient - M.beltramiCoefficient‖ /
    (1 - ‖M.beltramiCoefficient‖)
  let K := (1 + d) / (1 - d)
  have hfK : LiZhongQC.IsKQCRS f.toHomeomorph K :=
    MarkedRiemannSurface.relativeSmooth_isKQCRS M N hd
  have hf : LiZhongQC.IsQCRS f.toHomeomorph := ⟨K, hfK⟩
  have hcompat : ContinuousMap.Homotopic
      ((M.toSource.marking.trans f.toHomeomorph : X ≃ₜ N.toSource.X.carrier) :
        C(X, N.toSource.X.carrier))
      ((N.toSource.marking : X ≃ₜ N.toSource.X.carrier) :
        C(X, N.toSource.X.carrier)) := by
    have heq :
        ((M.toSource.marking.trans f.toHomeomorph : X ≃ₜ N.toSource.X.carrier) :
          C(X, N.toSource.X.carrier)) =
        ((N.toSource.marking : X ≃ₜ N.toSource.X.carrier) :
          C(X, N.toSource.X.carrier)) := by
      ext x
      change N.marking.toHomeomorph
        (M.marking.toHomeomorph.symm (M.marking.toHomeomorph x)) = N.marking.toHomeomorph x
      rw [M.marking.toHomeomorph.symm_apply_apply]
    simpa only [heq] using
      ContinuousMap.Homotopic.refl
        ((N.toSource.marking : X ≃ₜ N.toSource.X.carrier) : C(X, N.toSource.X.carrier))
  have hmem : Real.log (LiZhongQC.maxDilatationRS f.toHomeomorph).toReal ∈
      QCBookMetric.admissibleLogDilatations (toSource R (mk M)) (toSource R (mk N)) :=
    ⟨M.toSource, N.toSource, f.toHomeomorph, rfl, rfl, hf, hcompat, rfl⟩
  have hmax : (LiZhongQC.maxDilatationRS f.toHomeomorph).toReal ≤ K := by
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (LiZhongQC.maxDilatationRS_le hfK)
    simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hfK.1)] using hle
  have hpos : 0 < (LiZhongQC.maxDilatationRS f.toHomeomorph).toReal :=
    zero_lt_one.trans_le (LiZhongQC.s29_m_one_le_toReal hf)
  change sInf (QCBookMetric.admissibleLogDilatations
    (toSource R (mk M)) (toSource R (mk N))) ≤ Real.log K
  exact (csInf_le (QCBookMetric.admissibleLogDilatations_bddBelow _ _) hmem).trans
    (Real.log_le_log hpos hmax)

end TeichmullerSpace

namespace RealizedBeltramiCoefficients

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

theorem beta_fromQCDistance_le_log_relative
    (μ ν : RealizedBeltramiCoefficients.{u, u} R)
    (hd : ‖ν.val - μ.val‖ / (1 - ‖μ.val‖) < 1) :
    TeichmullerSpace.fromQCDistance R (beta μ) (beta ν) ≤
      Real.log ((1 + ‖ν.val - μ.val‖ / (1 - ‖μ.val‖)) /
        (1 - ‖ν.val - μ.val‖ / (1 - ‖μ.val‖))) := by
  change TeichmullerSpace.fromQCDistance R
    (TeichmullerSpace.mk μ.representative) (TeichmullerSpace.mk ν.representative) ≤ _
  have hm := representative_coefficient μ
  have hn := representative_coefficient ν
  have hbound := TeichmullerSpace.fromQCDistance_mk_le_log_relative R
    μ.representative ν.representative (by simpa only [hm, hn] using hd)
  simpa only [hm, hn] using hbound

/-- The actual coefficient projection is continuous into the explicit QC metric
 topology. This does not silently replace its separately defined quotient topology. -/
theorem continuous_beta_fromQCMetric {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g) :
    @Continuous (RealizedBeltramiCoefficients.{u, u} R) (TeichmullerSpace.{u, u} R)
      inferInstance
      ((TeichmullerSpace.fromQCMetricSpace R hg hgenus
          hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
      beta := by
  let m := TeichmullerSpace.fromQCMetricSpace R hg hgenus hPresentation
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : MetricSpace (TeichmullerSpace.{u, u} R) := m
  apply Metric.continuous_iff.2
  intro μ ε hε
  obtain ⟨t, ht0, ht1, htε⟩ := LiZhongQC.aw_t_log_small hε
  have hbase : 0 < 1 - ‖μ.val‖ := sub_pos.mpr (norm_lt_one μ)
  refine ⟨(1 - ‖μ.val‖) * t, mul_pos hbase ht0, ?_⟩
  intro ν hν
  have hdiff : ‖ν.val - μ.val‖ < (1 - ‖μ.val‖) * t := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hν
  let d := ‖ν.val - μ.val‖ / (1 - ‖μ.val‖)
  have hd0 : 0 ≤ d := div_nonneg (norm_nonneg _) hbase.le
  have hdt : d < t := (div_lt_iff₀ hbase).2 (by simpa only [mul_comm] using hdiff)
  have hd1 : d < 1 := hdt.trans ht1
  have hratio : (1 + d) / (1 - d) ≤ (1 + t) / (1 - t) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hd1) (sub_pos.mpr ht1)).2
    nlinarith
  have hlog : Real.log ((1 + d) / (1 - d)) < ε :=
    (Real.log_le_log (div_pos (by linarith : 0 < 1 + d) (sub_pos.mpr hd1))
      hratio).trans_lt htε
  calc
    dist (beta ν) (beta μ) = dist (beta μ) (beta ν) := dist_comm _ _
    _ ≤ Real.log ((1 + d) / (1 - d)) := by
      change TeichmullerSpace.fromQCDistance R (beta μ) (beta ν) ≤ _
      exact beta_fromQCDistance_le_log_relative μ ν hd1
    _ < ε := hlog

end RealizedBeltramiCoefficients

end LowDimensionalTopology.Geometry.Teichmuller
