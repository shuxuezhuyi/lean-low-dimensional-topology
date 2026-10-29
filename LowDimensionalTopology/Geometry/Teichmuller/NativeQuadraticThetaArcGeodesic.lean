module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothPath

/-!
# Actual native geodesics from smooth fixed-phase arcs

The original source path has a smooth chart subdivision and is a regular
fixed-phase arc in the interior. Its continuous endpoints may be zeros. The
existing shortest-arc comparison is applied to every actual competitor, while
the native interval identity retains the original parameter and path infimum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- An actual source-smooth fixed-phase arc is a local geodesic of the same
native lifted quadratic differential, including when its endpoints are zeros. -/
theorem native_smooth_thetaArc_isPhiGeodesic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b) (θ : ℝ),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        IsHorizontalArc (fun z => Complex.exp (-(θ : ℂ) * Complex.I) * ψ z)
          (fun t : ℝ => (L.extend t : ℂ)) 0 1 →
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) L := by
  classical
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b L θ hSmooth hTheta
  let u : ℂ := Complex.exp (-(θ : ℂ) * Complex.I)
  let φ : ℂ → ℂ := fun z => u * ψ z
  have hunit : ‖u‖ = 1 := by
    simpa only [u, Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I (-θ)
  have hρ (z : ℂ) : phiDensity φ z = phiDensity ψ z := by
    simp only [phiDensity, φ, norm_mul, hunit, one_mul]
  have hφ : DifferentiableOn ℂ φ upperHalf :=
    (utm_liftQD_differentiableOn q.property hp).const_mul u
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := by
    intro hzero
    exact hq (Subtype.ext hzero)
  have hφne : ∃ z ∈ upperHalf, φ z ≠ 0 := by
    obtain ⟨z, hz, hψz⟩ := utm_liftQD_ne q.property hqfun hp
    exact ⟨z, hz, mul_ne_zero (Complex.exp_ne_zero _) hψz⟩
  have hLfinite := quadraticLengthPath_lt_top_of_piecewiseSmooth
    upperHalfNativeSurface qH L hSmooth
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top
    (qH : UpperHalfPlane → ℂ → ℂ) L hLfinite
  intro _t₀ _ht₀
  refine ⟨2, by norm_num, ?_⟩
  intro s hs t ht _hlo hst _hhi
  have hLIntegral := liftedQuadraticLengthOn_eq_integral_of_lipschitz
    R.toRiemannSurface q hp a b L s t hs.1 hst ht.2
      ⟨K, hK.mono (Icc_subset_Icc hs.1 ht.2)⟩
  apply le_antisymm
  · unfold phiDistRS
    refine le_iInf fun δ => ?_
    rw [hLIntegral]
    by_cases htop : phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨B, hB⟩ := nativeH_lipschitz_of_length_lt_top
      (qH : UpperHalfPlane → ℂ → ℂ) δ (lt_top_iff_ne_top.mpr htop)
    let β : LRCurve := ⟨fun v : ℝ => (δ.extend v : ℂ), fun _ _ =>
      ⟨B, Icc (0 : ℝ) 1,
        Filter.mem_of_superset self_mem_nhdsWithin Ioo_subset_Icc_self, hB⟩⟩
    have hβH : β.trace ⊆ upperHalf := by
      rintro _ ⟨v, _, rfl⟩
      exact (δ.extend v).im_pos
    have hδcont : Continuous (fun v : ℝ => (δ.extend v : ℂ)) :=
      UpperHalfPlane.continuous_coe.comp δ.continuous_extend
    have hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (L.extend s : ℂ)) := by
      have hlim : Tendsto (fun v : ℝ => (δ.extend v : ℂ))
          (𝓝[>] 0) (𝓝 (δ.extend 0 : ℂ)) :=
        hδcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [β, Path.extend_zero] using hlim
    have hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (L.extend t : ℂ)) := by
      have hlim : Tendsto (fun v : ℝ => (δ.extend v : ℂ))
          (𝓝[<] 1) (𝓝 (δ.extend 1 : ℂ)) :=
        hδcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [β, Path.extend_one] using hlim
    have hδIntegral := liftedQuadraticLengthOn_eq_integral_of_lipschitz
      R.toRiemannSurface q hp (L.extend s) (L.extend t) δ 0 1
        le_rfl zero_lt_one le_rfl ⟨B, hB⟩
    have hβLength : phiLength φ β = phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
      simpa only [phiLength, LRCurve.rhoLength, β, hρ, phiLengthPath] using hδIntegral.symm
    have hθst : IsHorizontalArc φ (fun v : ℝ => (L.extend v : ℂ)) s t := by
      intro v hv
      exact hTheta v ⟨hs.1.trans_lt hv.1, hv.2.trans_le ht.2⟩
    have hcont : ContinuousOn (fun v : ℝ => (L.extend v : ℂ)) (Icc s t) :=
      (UpperHalfPlane.continuous_coe.comp L.continuous_extend).continuousOn
    have hH : (fun v : ℝ => (L.extend v : ℂ)) '' Icc s t ⊆ upperHalf := by
      rintro _ ⟨v, _, rfl⟩
      exact (L.extend v).im_pos
    have hshort := utm_arc_shortest_upperHalf hφ hφne hst hθst hcont hH β hβH hβa hβb
    simpa only [hρ, hβLength] using hshort
  · obtain ⟨β, _, hβ⟩ :=
      s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) L hs.1 hst ht.2
    exact le_trans
      (iInf_le (fun δ : Path (L.extend s) (L.extend t) =>
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ) β) hβ

end LowDimensionalTopology.Geometry.Teichmuller
