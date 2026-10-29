/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Finite minima of the actual lifted quadratic length

The local replacement proof for a finite minimum uses the actual local shortest
connectors and chart-disc splicing. It applies on the native upper half-plane
with the same lifted differential and all original path competitors.

The local proof is adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
LiZhongQC/Ch07/S25_QuadraticDifferentials.lean, shortest_isPhiGeodesicRS,
fixed commit 1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private theorem finite_allPathMinimum_isPhiGeodesic
    {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {a b : S} {γ : Path a b}
    (hγ : ∀ γ' : Path a b, phiLengthPath q γ ≤ phiLengthPath q γ')
    (hfin : phiLengthPath q γ < ⊤) : IsPhiGeodesicRS q γ := by
  classical
  intro t₀ ht₀
  obtain ⟨r, hr0, hrt, V, hV, hVW, hloc⟩ := s25i_local hq hne (γ.extend t₀)
  have hpre : γ.extend ⁻¹' V ∈ 𝓝 t₀ := γ.continuous_extend.continuousAt.preimage_mem_nhds hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨δ, hδ, fun s hs t ht h1 hst h2 => ?_⟩
  have hmem : ∀ u ∈ Icc s t, γ.extend u ∈ V := fun u hu => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2])
  have hsV := hmem s ⟨le_rfl, hst.le⟩
  have htV := hmem t ⟨hst.le, le_rfl⟩
  obtain ⟨σ, hσW, hσl⟩ := hloc _ hsV _ htV
  apply le_antisymm
  · obtain ⟨γ', _, hγ'l⟩ := s25i_splice γ (γ.extend t₀) hrt hs.1 hst ht.2
      (by rintro _ ⟨x, hx, rfl⟩; exact hVW (hmem x hx)) σ hσW
    have h1 := hγ γ'
    have hfin' : phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 ≤ phiLengthPath q γ := by
      unfold phiLengthPath
      have e1 := s25i_split_ge (q := q) γ (x := 0) (y := s) (z := t) hs.1 hst.le
      have e2 := s25i_split_ge (q := q) γ (x := 0) (y := t) (z := 1) (hs.1.trans hst.le) ht.2
      exact (add_le_add_left e1 _).trans e2
    have hA : phiLengthOn q γ 0 s + phiLengthOn q γ t 1 ≠ ⊤ := by
      refine ne_top_of_le_ne_top hfin.ne ?_
      calc phiLengthOn q γ 0 s + phiLengthOn q γ t 1 ≤
            phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 := by
            rw [add_right_comm]; exact le_self_add
        _ ≤ _ := hfin'
    rw [← hσl]
    have h3 : phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 ≤
        phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 :=
      hfin'.trans (h1.trans hγ'l)
    refine (ENNReal.add_le_add_iff_right hA).1 ?_
    calc phiLengthOn q γ s t + (phiLengthOn q γ 0 s + phiLengthOn q γ t 1) =
          phiLengthOn q γ 0 s + phiLengthOn q γ s t + phiLengthOn q γ t 1 := by ring
      _ ≤ phiLengthOn q γ 0 s + phiLengthPath q σ + phiLengthOn q γ t 1 := h3
      _ = phiLengthPath q σ + (phiLengthOn q γ 0 s + phiLengthOn q γ t 1) := by ring
  · obtain ⟨β, hβW, hβl⟩ := s25i_subpath_length (q := q) γ hs.1 hst ht.2
    exact (iInf_le _ β).trans hβl

/-- A finite global minimum among all original paths is a local geodesic
of the same native lifted quadratic differential, also at zero endpoints. -/
theorem native_finite_allPathMinimum_isPhiGeodesic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) L < ⊤ →
        (∀ δ : Path a b, phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) L ≤
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ) →
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) L := by
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
  intro a b L hfinite hmin
  have hqne : (q : X → ℂ → ℂ) ≠ 0 := by
    intro hzero
    exact hq (Subtype.ext hzero)
  obtain ⟨z, hz, hψz⟩ := utm_liftQD_ne q.property hqne hp
  have hqHne : (qH : UpperHalfPlane → ℂ → ℂ) ≠ 0 := by
    intro hzero
    have heq : (qH : UpperHalfPlane → ℂ → ℂ) ⟨z, hz⟩ z = 0 :=
      congrFun (congrFun hzero ⟨z, hz⟩) z
    change upperHalf.indicator ψ z = 0 at heq
    rw [Set.indicator_of_mem hz] at heq
    exact hψz heq
  exact finite_allPathMinimum_isPhiGeodesic qH.property hqHne hmin hfinite

end LowDimensionalTopology.Geometry.Teichmuller
