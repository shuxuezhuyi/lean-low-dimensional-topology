module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeZeroJoinCost
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHorizontalSideSegment
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticSmoothSubpath

/-!
# Actual zero-endpoint rays of two original horizontal sides

The proper sides are literal subpaths of the original source-smooth path.
The explicit endpoint-ray input supplies their images in the same normalized
coordinate. Only pointwise affine clock identities transfer those images back
to the original parameter; the native weighted integral is never reparametrized.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

private theorem subpath_endpoint_ray_pullback
    {a b : UpperHalfPlane} (δ : Path a b) (s t : unitInterval) (hst : s < t)
    (first : Bool) (ξ : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (v : ℂ)
    (hray : ∀ u ∈ Icc (0 : ℝ) ε, ∃ ρ : ℝ, 0 ≤ ρ ∧
      ξ ((δ.subpath s t).extend (if first then u else 1 - u) : ℂ) = (ρ : ℂ) * v) :
    ∃ η : ℝ, 0 < η ∧ η ≤ (t : ℝ) - s ∧
      ∀ u ∈ Icc (0 : ℝ) η, ∃ ρ : ℝ, 0 ≤ ρ ∧
        ξ (δ.extend (if first then (s : ℝ) + u else (t : ℝ) - u) : ℂ) =
          (ρ : ℂ) * v := by
  let d : ℝ := (t : ℝ) - s
  have hd : 0 < d := sub_pos.mpr hst
  have hcomb (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (Icc.convexComb s t ⟨u, hu⟩ : ℝ) = d * u + s := by
    rw [Icc.coe_convexComb]
    dsimp only [d]
    ring
  have hext (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (δ.subpath s t).extend u = δ.extend (d * u + s) := by
    have hunit : d * u + (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
      rw [← hcomb u hu]
      exact (Icc.convexComb s t ⟨u, hu⟩).property
    rw [Path.extend_apply (δ.subpath s t) hu]
    change δ (Icc.convexComb s t ⟨u, hu⟩) = δ.extend (d * u + s)
    rw [Path.extend_apply δ hunit]
    exact congrArg δ (Subtype.ext (hcomb u hu))
  have hηd : d * ε ≤ d := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hε1 hd.le
  refine ⟨d * ε, mul_pos hd hε, hηd, ?_⟩
  intro u hu
  have hv0 : 0 ≤ u / d := div_nonneg hu.1 hd.le
  have hvε : u / d ≤ ε := (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hu.2)
  have hv1 : u / d ≤ 1 := hvε.trans hε1
  have hpar : (if first then u / d else 1 - u / d) ∈ Icc (0 : ℝ) 1 := by
    cases first
    · change 1 - u / d ∈ Icc (0 : ℝ) 1
      constructor <;> linarith
    · exact ⟨hv0, hv1⟩
  have hmul : d * (u / d) = u := mul_div_cancel₀ u hd.ne'
  have hclock : d * (if first then u / d else 1 - u / d) + (s : ℝ) =
      (if first then (s : ℝ) + u else (t : ℝ) - u) := by
    cases first
    · change d * (1 - u / d) + (s : ℝ) = (t : ℝ) - u
      rw [mul_sub, mul_one, hmul]
      dsimp only [d]
      ring
    · change d * (u / d) + (s : ℝ) = (s : ℝ) + u
      rw [hmul, add_comm]
  obtain ⟨ρ, hρ, heq⟩ := hray (u / d) ⟨hv0, hvε⟩
  refine ⟨ρ, hρ, ?_⟩
  rw [hext _ hpar, hclock] at heq
  exact heq

/-- The two actual proper horizontal sides of the same source-smooth path
are locally minimizing across their common zero, using the explicit zero-ray input. -/
theorem native_horizontal_zero_join_crossing_minimum
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
      ∀ {a b : UpperHalfPlane} (δ : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface δ →
        ∀ l τ r : unitInterval, l < τ → τ < r → InjOn δ (Icc l r) →
          IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (l : ℝ) τ →
          IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (τ : ℝ) r →
          ∀ (m : ℕ), 0 < m → ∀ ξ : ℂ → ℂ,
            (AnalyticAt ℂ ξ (δ.extend τ : ℂ) ∧ ξ (δ.extend τ : ℂ) = 0 ∧
              deriv ξ (δ.extend τ : ℂ) ≠ 0 ∧
              ∀ᶠ z in 𝓝 (δ.extend τ : ℂ),
                ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
            ∃ ε > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
              (τ : ℝ) - ε < s → s < τ → (τ : ℝ) < t → t < τ + ε →
                phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t =
                  phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (δ.extend s) (δ.extend t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ hSmooth l τ r hlτ hτr hi hL hR m hm ξ hξ
  have hξat := hξ
  simp only [Path.extend_apply δ τ.property] at hξat
  obtain ⟨hξa, hξ0, hξd, hξq⟩ := hξat
  have hψτ : ψ (δ τ : ℂ) = 0 := by
    have h := hξq.self_of_nhds
    rw [hξ0, zero_pow hm.ne', mul_zero, zero_mul] at h
    exact h
  have hSmoothL := hSmooth.subpath_of_lt l τ hlτ
  have hSmoothR := hSmooth.subpath_of_lt τ r hτr
  have hSegL := native_horizontal_subpath_isQuadraticSegment R q hp δ l τ hlτ
    (hi.mono (Icc_subset_Icc le_rfl hτr.le)) hL
  have hSegR := native_horizontal_subpath_isQuadraticSegment R q hp δ τ r hτr
    (hi.mono (Icc_subset_Icc hlτ.le le_rfl)) hR
  obtain ⟨εL, hεL, hεL1, vL, hvL, hRayL⟩ :=
    hzero R q hq hp (δ.subpath l τ) hSmoothL hSegL false hψτ
      m hm ξ hξa hξ0 hξd hξq
  obtain ⟨εR, hεR, hεR1, vR, hvR, hRayR⟩ :=
    hzero R q hq hp (δ.subpath τ r) hSmoothR hSegR true hψτ
      m hm ξ hξa hξ0 hξd hξq
  obtain ⟨ηL, hηL, hηLl, hleftRay⟩ :=
    subpath_endpoint_ray_pullback δ l τ hlτ false ξ εL hεL hεL1 vL hRayL
  obtain ⟨ηR, hηR, hηRr, hrightRay⟩ :=
    subpath_endpoint_ray_pullback δ τ r hτr true ξ εR hεR hεR1 vR hRayR
  let l' : ℝ := τ - ηL
  let r' : ℝ := τ + ηR
  have hll' : (l : ℝ) ≤ l' := by dsimp only [l']; linarith
  have hl'0 : 0 ≤ l' := l.property.1.trans hll'
  have hl'τ : l' < τ := by dsimp only [l']; linarith
  have hr'r : r' ≤ (r : ℝ) := by dsimp only [r']; linarith
  have hr'1 : r' ≤ 1 := hr'r.trans r.property.2
  have hτr' : (τ : ℝ) < r' := by dsimp only [r']; linarith
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top
    (qH : UpperHalfPlane → ℂ → ℂ) δ
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH δ hSmooth)
  have hLip : ∃ K : NNReal,
      LipschitzOnWith K (fun u : ℝ => (δ.extend u : ℂ)) (Icc l' r') :=
    ⟨K, hK.mono (Icc_subset_Icc hl'0 hr'1)⟩
  have hiF : InjOn (fun u : ℝ => (δ.extend u : ℂ)) (Icc l' r') := by
    intro u hu v hv heq
    have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hl'0.trans hu.1, hu.2.trans hr'1⟩
    have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨hl'0.trans hv.1, hv.2.trans hr'1⟩
    have hpath : δ ⟨u, hu01⟩ = δ ⟨v, hv01⟩ := by
      simpa only [Path.extend_apply δ hu01, Path.extend_apply δ hv01]
        using UpperHalfPlane.coe_injective heq
    exact congrArg (fun x : unitInterval => (x : ℝ))
      (hi ⟨hll'.trans hu.1, hu.2.trans hr'r⟩ ⟨hll'.trans hv.1, hv.2.trans hr'r⟩ hpath)
  have hL' : IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) l' τ := by
    intro u hu
    exact hL u ⟨hll'.trans_lt hu.1, hu.2⟩
  have hR' : IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) (τ : ℝ) r' := by
    intro u hu
    exact hR u ⟨hu.1, hu.2.trans_le hr'r⟩
  have hrL : ∀ u ∈ Icc l' (τ : ℝ), ∃ ρ : ℝ, 0 ≤ ρ ∧
      ξ (δ.extend u : ℂ) = (ρ : ℂ) * vL := by
    intro u hu
    have hpar : (τ : ℝ) - u ∈ Icc (0 : ℝ) ηL := by
      dsimp only [l'] at hu
      constructor <;> linarith [hu.1, hu.2]
    obtain ⟨ρ, hρ, heq⟩ := hleftRay ((τ : ℝ) - u) hpar
    refine ⟨ρ, hρ, ?_⟩
    change ξ (δ.extend ((τ : ℝ) - (τ - u)) : ℂ) = (ρ : ℂ) * vL at heq
    simpa only [show (τ : ℝ) - (τ - u) = u by ring] using heq
  have hrR : ∀ u ∈ Icc (τ : ℝ) r', ∃ ρ : ℝ, 0 ≤ ρ ∧
      ξ (δ.extend u : ℂ) = (ρ : ℂ) * vR := by
    intro u hu
    have hpar : u - (τ : ℝ) ∈ Icc (0 : ℝ) ηR := by
      dsimp only [r'] at hu
      constructor <;> linarith [hu.1, hu.2]
    obtain ⟨ρ, hρ, heq⟩ := hrightRay (u - (τ : ℝ)) hpar
    refine ⟨ρ, hρ, ?_⟩
    change ξ (δ.extend ((τ : ℝ) + (u - τ)) : ℂ) = (ρ : ℂ) * vR at heq
    simpa only [show (τ : ℝ) + (u - τ) = u by ring] using heq
  exact native_zero_join_cost_transfer R q hq hp δ
    hl'0 hl'τ hτr' hr'1 hLip hiF m hm ξ hξ vL vR hvL hvR hL' hR' hrL hrR

end LowDimensionalTopology.Geometry.Teichmuller
