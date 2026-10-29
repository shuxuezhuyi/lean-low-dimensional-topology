module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHorizontalZeroJoin
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticThetaArcGeodesic

/-!
# Finite horizontal cycles in the same native quadratic metric

Only finite cuts, the original source-smooth path and its actual horizontal
open sides are supplied. Original interval comparisons cover ordinary windows
and one-sided endpoints. Proper internal windows use the actual zero-ray input
and the existing normalized-coordinate comparison for the same path.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

private theorem native_horizontal_interval_minimum
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (δ : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ →
        ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
          IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) s t →
          phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t =
            phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (δ.extend s) (δ.extend t) := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ hSmooth s t hs hst ht hH
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := by
    intro h
    exact hq (Subtype.ext h)
  have hψne := utm_liftQD_ne q.property hqfun hp
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top
    (qH : UpperHalfPlane → ℂ → ℂ) δ
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH δ hSmooth)
  have hIntegral := liftedQuadraticLengthOn_eq_integral_of_lipschitz
    R.toRiemannSurface q hp a b δ s t hs hst ht
      ⟨K, hK.mono (Icc_subset_Icc hs ht)⟩
  apply le_antisymm
  · unfold phiDistRS
    refine le_iInf fun η => ?_
    rw [hIntegral]
    by_cases htop : phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) η = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨B, hB⟩ := nativeH_lipschitz_of_length_lt_top
      (qH : UpperHalfPlane → ℂ → ℂ) η (lt_top_iff_ne_top.mpr htop)
    let β : LRCurve := ⟨fun v : ℝ => (η.extend v : ℂ), fun _ _ =>
      ⟨B, Icc (0 : ℝ) 1,
        Filter.mem_of_superset self_mem_nhdsWithin Ioo_subset_Icc_self, hB⟩⟩
    have hβH : β.trace ⊆ upperHalf := by
      rintro _ ⟨v, _, rfl⟩
      exact (η.extend v).im_pos
    have hηcont : Continuous (fun v : ℝ => (η.extend v : ℂ)) :=
      UpperHalfPlane.continuous_coe.comp η.continuous_extend
    have hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (δ.extend s : ℂ)) := by
      have hlim : Tendsto (fun v : ℝ => (η.extend v : ℂ))
          (𝓝[>] 0) (𝓝 (η.extend 0 : ℂ)) :=
        hηcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [β, Path.extend_zero] using hlim
    have hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (δ.extend t : ℂ)) := by
      have hlim : Tendsto (fun v : ℝ => (η.extend v : ℂ))
          (𝓝[<] 1) (𝓝 (η.extend 1 : ℂ)) :=
        hηcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [β, Path.extend_one] using hlim
    have hηIntegral := liftedQuadraticLengthOn_eq_integral_of_lipschitz
      R.toRiemannSurface q hp (δ.extend s) (δ.extend t) η 0 1
        le_rfl zero_lt_one le_rfl ⟨B, hB⟩
    have hβLength : phiLength ψ β = phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) η := by
      simpa only [phiLength, LRCurve.rhoLength, β, phiLengthPath] using hηIntegral.symm
    have hcont : ContinuousOn (fun v : ℝ => (δ.extend v : ℂ)) (Icc s t) :=
      (UpperHalfPlane.continuous_coe.comp δ.continuous_extend).continuousOn
    have hHsrc : (fun v : ℝ => (δ.extend v : ℂ)) '' Icc s t ⊆ upperHalf := by
      rintro _ ⟨v, _, rfl⟩
      exact (δ.extend v).im_pos
    have hshort := utm_arc_shortest_upperHalf
      (utm_liftQD_differentiableOn q.property hp) hψne hst hH hcont hHsrc β hβH hβa hβb
    exact hshort.trans hβLength.le
  · obtain ⟨η, _, hη⟩ :=
      s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) δ hs hst ht
    exact (iInf_le _ η).trans hη

private theorem native_positive_order_zero_coordinate
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      ∀ z₀ : UpperHalfPlane, ψ (z₀ : ℂ) = 0 →
        ∃ m : ℕ, 0 < m ∧ ∃ ξ : ℂ → ℂ,
          AnalyticAt ℂ ξ (z₀ : ℂ) ∧ ξ (z₀ : ℂ) = 0 ∧ deriv ξ (z₀ : ℂ) ≠ 0 ∧
            ∀ᶠ z in 𝓝 (z₀ : ℂ),
              ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let := upperHalfNativeSurface.t2Space
  let := upperHalfNativeSurface.connectedSpace
  let := upperHalfNativeSurface.toRiemannAtlas.isManifold
  dsimp only
  intro z₀ hz₀
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := by
    intro h
    exact hq (Subtype.ext h)
  obtain ⟨z, hz, hψz⟩ := utm_liftQD_ne q.property hqfun hp
  have hqHne : (qH : UpperHalfPlane → ℂ → ℂ) ≠ 0 := by
    intro h
    have heq : (qH : UpperHalfPlane → ℂ → ℂ) ⟨z, hz⟩ z = 0 :=
      congrFun (congrFun h ⟨z, hz⟩) z
    change upperHalf.indicator ψ z = 0 at heq
    rw [Set.indicator_of_mem hz] at heq
    exact hψz heq
  obtain ⟨m, ξ, hξa, hξ0, hξd, hξq⟩ := s25e_natural_chart qH.property hqHne z₀
  have hchart : chartAt ℂ z₀ = UpperHalfPlane.ofComplex.symm := by
    have h := chart_mem_atlas ℂ z₀
    change chartAt ℂ z₀ ∈ ({UpperHalfPlane.ofComplex.symm} :
      Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at h
    exact Set.mem_singleton_iff.mp h
  have hcenter : chartAt ℂ z₀ z₀ = (z₀ : ℂ) := by rw [hchart]; rfl
  rw [hcenter] at hξa hξ0 hξd hξq
  have hξψ : ∀ᶠ z in 𝓝 (z₀ : ℂ),
      ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
    filter_upwards [hξq, isOpen_upperHalf.mem_nhds z₀.im_pos] with z hz hzH
    change upperHalf.indicator ψ z = _ at hz
    rwa [Set.indicator_of_mem hzH] at hz
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst m
    have h := hξψ.self_of_nhds
    norm_num at h
    have hψzero : ψ (z₀ : ℂ) = 0 := hz₀
    rw [hψzero] at h
    exact False.elim ((pow_ne_zero 2 hξd) h.symm)
  · exact ⟨m, hm, ξ, hξa, hξ0, hξd, hξψ⟩

/-- A finite embedded cycle of actual horizontal sides, with its genuine zero
cuts and original smooth subdivision, is locally geodesic in the same native metric. -/
theorem native_finite_horizontal_cycle_isPhiGeodesic
    (hzero : NativeQuadraticZeroEndpointRay)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a : UpperHalfPlane} (δ : Path a a),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ →
        InjOn δ (Ico (0 : unitInterval) 1) →
        ∀ (n : ℕ), 0 < n → ∀ cuts : Fin (n + 1) → unitInterval,
          StrictMono cuts → cuts 0 = 0 → cuts (Fin.last n) = 1 →
          (∀ i : Fin (n + 1), 0 < i.val → i.val < n → ψ (δ (cuts i) : ℂ) = 0) →
          (∀ i : Fin n, IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ))
            (cuts i.castSucc : ℝ) (cuts i.succ : ℝ)) →
          IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a δ hSmooth hi n hn cuts hc h0 h1 hz hh
  let : NeZero n := ⟨hn.ne'⟩
  by_cases hn1 : n = 1
  · subst n
    have hH : IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) 0 1 := by
      have h := hh (0 : Fin 1)
      change IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ))
        (cuts 0 : ℝ) (cuts (Fin.last 1) : ℝ) at h
      simpa only [h0, h1, Set.Icc.coe_zero, Set.Icc.coe_one] using h
    apply native_smooth_thetaArc_isPhiGeodesic R q hq hp δ 0 hSmooth
    simpa only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using hH
  have hcover (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
      ∃ i : Fin n, (cuts i.castSucc : ℝ) ≤ v ∧ v < (cuts i.succ : ℝ) := by
    let J : Finset (Fin (n + 1)) := Finset.univ.filter fun j => v < (cuts j : ℝ)
    have hJ : J.Nonempty := ⟨Fin.last n, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa only [h1, Set.Icc.coe_one] using hv1⟩⟩
    let j : Fin (n + 1) := J.min' hJ
    have hj : v < (cuts j : ℝ) := (Finset.mem_filter.mp (Finset.min'_mem J hJ)).2
    have hjpos : 0 < j.val := by
      by_contra h
      have hj0 : j = 0 := by apply Fin.ext; rw [Fin.val_zero]; omega
      rw [hj0, h0] at hj
      exact (not_lt_of_ge hv0) hj
    let i : Fin n := ⟨j.val - 1, by have hjlt := j.is_lt; omega⟩
    have hiSucc : i.succ = j := by
      apply Fin.ext
      rw [Fin.val_succ]
      dsimp only [i]
      omega
    have hiLt : i.castSucc < j := by change i.val < j.val; dsimp only [i]; omega
    have hprev : (cuts i.castSucc : ℝ) ≤ v := by
      by_contra h
      have hiJ : i.castSucc ∈ J := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_of_not_ge h⟩
      have hmin : j ≤ i.castSucc := Finset.min'_le J _ hiJ
      exact (not_lt_of_ge hmin) hiLt
    exact ⟨i, hprev, by simpa only [hiSucc] using hj⟩
  intro t₀ ht₀
  by_cases ht1 : t₀ = 1
  · subst t₀
    let i : Fin n := ⟨n - 1, by omega⟩
    have hiSucc : i.succ = Fin.last n := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_last]
      dsimp only [i]
      omega
    have hEnd : (cuts i.succ : ℝ) = 1 := by simp only [hiSucc, h1, Set.Icc.coe_one]
    have hgap : (cuts i.castSucc : ℝ) < 1 := by
      rw [← hEnd]
      exact hc (by change i.val < i.val + 1; omega)
    refine ⟨1 - (cuts i.castSucc : ℝ), sub_pos.mpr hgap, ?_⟩
    intro s hs t ht hlo hst _hhi
    have hsCut : (cuts i.castSucc : ℝ) < s := by linarith
    apply native_horizontal_interval_minimum R q hq hp δ hSmooth s t hs.1 hst ht.2
    intro u hu
    exact hh i u ⟨hsCut.trans hu.1, by rw [hEnd]; exact hu.2.trans_le ht.2⟩
  have htlt : t₀ < 1 := lt_of_le_of_ne ht₀.2 ht1
  obtain ⟨i, hil, hir⟩ := hcover t₀ ht₀.1 htlt
  rcases eq_or_lt_of_le hil with hEq | hInterior
  · subst t₀
    by_cases hi0 : i.val = 0
    · have hiEq : i = 0 := Fin.ext hi0
      have hStart : (cuts i.castSucc : ℝ) = 0 := by
        simp only [hiEq, Fin.castSucc_zero, h0, Set.Icc.coe_zero]
      have hNext : 0 < (cuts i.succ : ℝ) := by simpa only [hStart] using hir
      refine ⟨(cuts i.succ : ℝ), hNext, ?_⟩
      intro s hs t ht _hlo hst hhi
      have htCut : t < (cuts i.succ : ℝ) := by simpa only [hStart, zero_add] using hhi
      apply native_horizontal_interval_minimum R q hq hp δ hSmooth s t hs.1 hst ht.2
      intro u hu
      exact hh i u ⟨by rw [hStart]; exact hs.1.trans_lt hu.1, hu.2.trans htCut⟩
    have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
    let j : Fin n := ⟨i.val - 1, by have hiLt := i.is_lt; omega⟩
    have hjSucc : j.succ = i.castSucc := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc]
      dsimp only [j]
      omega
    let τ : unitInterval := cuts i.castSucc
    have hPrev : (cuts j.castSucc : ℝ) < τ :=
      hc (by change j.val < i.val; dsimp only [j]; omega)
    have hNext : (τ : ℝ) < cuts i.succ := hc (by change i.val < i.val + 1; omega)
    let l : unitInterval := ⟨((cuts j.castSucc : ℝ) + τ) / 2, by
      constructor <;> nlinarith [(cuts j.castSucc).property.1, (cuts j.castSucc).property.2,
        τ.property.1, τ.property.2]⟩
    let r : unitInterval := ⟨((τ : ℝ) + cuts i.succ) / 2, by
      constructor <;> nlinarith [τ.property.1, τ.property.2,
        (cuts i.succ).property.1, (cuts i.succ).property.2]⟩
    have hPrevL : (cuts j.castSucc : ℝ) < l := by change _ < (_ + (τ : ℝ)) / 2; linarith
    have hlτ : l < τ := by change (_ + (τ : ℝ)) / 2 < _; linarith
    have hτr : τ < r := by change (τ : ℝ) < (_ + _) / 2; linarith
    have hrNext : (r : ℝ) < cuts i.succ := by change (_ + _) / 2 < _; linarith
    have hr1 : r < 1 := hrNext.trans_le (cuts i.succ).property.2
    have hiWindow : InjOn δ (Icc l r) := hi.mono (by
      intro u hu
      exact ⟨u.property.1, hu.2.trans_lt hr1⟩)
    have hLeft : IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (l : ℝ) τ := by
      intro u hu
      have h := hh j
      rw [hjSucc] at h
      exact h u ⟨hPrevL.trans hu.1, hu.2⟩
    have hRight : IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (τ : ℝ) r := by
      intro u hu
      exact hh i u ⟨hu.1, hu.2.trans hrNext⟩
    have hzτ : ψ (δ τ : ℂ) = 0 := hz i.castSucc hiPos i.is_lt
    obtain ⟨m, hm, ξ, hξa, hξ0, hξd, hξq⟩ :=
      native_positive_order_zero_coordinate R q hq hp (δ τ) hzτ
    have hξat : AnalyticAt ℂ ξ (δ.extend τ : ℂ) ∧ ξ (δ.extend τ : ℂ) = 0 ∧
        deriv ξ (δ.extend τ : ℂ) ≠ 0 ∧
          ∀ᶠ z in 𝓝 (δ.extend τ : ℂ),
            ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2 := by
      simpa only [Path.extend_apply δ τ.property] using ⟨hξa, hξ0, hξd, hξq⟩
    obtain ⟨ε₀, hε₀, hcross⟩ := native_horizontal_zero_join_crossing_minimum
      hzero R q hq hp δ hSmooth l τ r hlτ hτr hiWindow hLeft hRight m hm ξ hξat
    let ε : ℝ := min ε₀ (min ((τ : ℝ) - l) ((r : ℝ) - τ))
    have hε : 0 < ε := lt_min hε₀ (lt_min (sub_pos.mpr hlτ) (sub_pos.mpr hτr))
    have hε₀' : ε ≤ ε₀ := min_le_left _ _
    have hεl : ε ≤ (τ : ℝ) - l := (min_le_right _ _).trans (min_le_left _ _)
    have hεr : ε ≤ (r : ℝ) - τ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ε, hε, ?_⟩
    intro s hs t ht hlo hst hhi
    have hsL : (l : ℝ) < s := by change (τ : ℝ) - ε < s at hlo; linarith
    have htR : t < (r : ℝ) := by change t < (τ : ℝ) + ε at hhi; linarith
    by_cases hsτ : s < τ
    · by_cases hτt : (τ : ℝ) < t
      · exact hcross s hs t ht (by change (τ : ℝ) - ε < s at hlo; linarith)
          hsτ hτt (by change t < (τ : ℝ) + ε at hhi; linarith)
      · have htτ : t ≤ τ := le_of_not_gt hτt
        apply native_horizontal_interval_minimum R q hq hp δ hSmooth s t hs.1 hst ht.2
        intro u hu
        exact hLeft u ⟨hsL.trans hu.1, hu.2.trans_le htτ⟩
    · have hτs : (τ : ℝ) ≤ s := le_of_not_gt hsτ
      apply native_horizontal_interval_minimum R q hq hp δ hSmooth s t hs.1 hst ht.2
      intro u hu
      exact hRight u ⟨hτs.trans_lt hu.1, hu.2.trans htR⟩
  · let ε : ℝ := min (t₀ - (cuts i.castSucc : ℝ)) ((cuts i.succ : ℝ) - t₀)
    have hε : 0 < ε := lt_min (sub_pos.mpr hInterior) (sub_pos.mpr hir)
    have hεL : ε ≤ t₀ - (cuts i.castSucc : ℝ) := min_le_left _ _
    have hεR : ε ≤ (cuts i.succ : ℝ) - t₀ := min_le_right _ _
    refine ⟨ε, hε, ?_⟩
    intro s hs t ht hlo hst hhi
    have hsCut : (cuts i.castSucc : ℝ) < s := by linarith
    have htCut : t < (cuts i.succ : ℝ) := by linarith
    apply native_horizontal_interval_minimum R q hq hp δ hSmooth s t hs.1 hst ht.2
    intro u hu
    exact hh i u ⟨hsCut.trans hu.1, hu.2.trans htCut⟩

end LowDimensionalTopology.Geometry.Teichmuller
