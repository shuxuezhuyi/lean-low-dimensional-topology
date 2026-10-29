/-
The finite-subinterval lifted-Lipschitz argument is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticSubintervalLiftLength

/-!
# Local quadratic geodesics under the actual uniformizing lift

Local finiteness of the original distance makes every sufficiently short
geodesic interval finite. Its actual lift is Lipschitz there, and the original
coefficient integral identifies its two native interval lengths. Projection
and the actual affine subpath provide the two distance bounds.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private theorem actualLift_lipschitzOn_of_intervalLength_lt_top
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ (_hp : IsUniformization Γ p) {a b : X} (γ : Path a b)
      (c : C(unitInterval, UpperHalfPlane)) (_hc : ∀ u, p (c u) = γ u) (s t : ℝ),
      phiLengthOn (q : X → ℂ → ℂ) γ s t < ⊤ →
      ∃ K : ℝ≥0, LipschitzOnWith K
        (fun u : ℝ => (c (Set.projIcc 0 1 zero_le_one u) : ℂ)) (Icc s t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp a b γ c hc s t hfinite
  unfold phiLengthOn at hfinite
  simp only [iInf_lt_iff] at hfinite
  obtain ⟨n, τ, x, hP, _⟩ := hfinite
  have hloc : ∀ i : Fin n, ∃ K : ℝ≥0, LipschitzOnWith K
      (fun u : ℝ => (c (Set.projIcc 0 1 zero_le_one u) : ℂ))
        (Icc (τ i.castSucc) (τ i.succ)) := by
    intro i
    obtain ⟨hsrc, K, hK⟩ := hP.2.2.2 i
    have h := utm_a_lift_locallyLipschitzOn q.property hp γ c hc (x i) hsrc hK
    exact h.exists_lipschitzOnWith_of_compact isCompact_Icc
  choose K hK using hloc
  have hpiece : ∀ i : Fin n, LipschitzOnWith (Finset.univ.sup K)
      (fun u : ℝ => (c (Set.projIcc 0 1 zero_le_one u) : ℂ))
        (Icc (τ i.castSucc) (τ i.succ)) := fun i =>
    (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  have hall : ∀ j : Fin (n + 1), LipschitzOnWith (Finset.univ.sup K)
      (fun u : ℝ => (c (Set.projIcc 0 1 zero_le_one u) : ℂ)) (Icc (τ 0) (τ j)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro u hu v hv
      have huv : u = v := le_antisymm (hu.2.trans hv.1) (hv.2.trans hu.1)
      rw [huv, edist_self]
      exact zero_le
    | succ i ih => exact utm_a_lipschitzOnWith_Icc_union ih (hpiece i)
  refine ⟨Finset.univ.sup K, ?_⟩
  have h := hall (Fin.last n)
  rwa [hP.1, hP.2.1] at h

/-- The entire actual continuous lift of an original local quadratic geodesic
is a local geodesic of the same native lifted quadratic differential. -/
theorem isPhiGeodesicRS_actualLift
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : X} (γ : Path a b) (c : C(unitInterval, UpperHalfPlane))
        (_hc : ∀ u, p (c u) = γ u),
        IsPhiGeodesicRS (q : X → ℂ → ℂ) γ →
        let δ : Path (c 0) (c 1) := ⟨c, rfl, rfl⟩
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b γ c hc hgeo
  let δ : Path (c 0) (c 1) := ⟨c, rfl, rfl⟩
  change IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ
  have hmap (u : ℝ) : p (δ.extend u) = γ.extend u :=
    hc (Set.projIcc 0 1 zero_le_one u)
  intro t₀ ht₀
  obtain ⟨r, hr, hshort⟩ := hgeo t₀ ht₀
  obtain ⟨W, hW, _, hWfinite⟩ := s25s_distance_local_control q.property (γ.extend t₀)
  have hpre : γ.extend ⁻¹' W ∈ 𝓝 t₀ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hnear (u : ℝ) (hlo : t₀ - min r ε < u) (hhi : u < t₀ + min r ε) :
      γ.extend u ∈ W := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hmin := min_le_right r ε
    constructor <;> linarith
  refine ⟨min r ε, lt_min hr hε, ?_⟩
  intro s hs t ht hlo hst hhi
  have hsr : t₀ - r < s := by linarith [min_le_left r ε]
  have htr : t < t₀ + r := by linarith [min_le_left r ε]
  have hseg := hshort s hs t ht hsr hst htr
  have hfinite : phiLengthOn (q : X → ℂ → ℂ) γ s t < ⊤ := by
    rw [hseg]
    exact hWfinite _ (hnear s hlo (hst.trans hhi)) _ (hnear t (hlo.trans hst) hhi)
  obtain ⟨K, hK⟩ := actualLift_lipschitzOn_of_intervalLength_lt_top R q hp γ c hc s t hfinite
  have hdown := quadraticLengthOn_eq_liftIntegral_of_lt_top R q γ c s t
    hp hc hs.1 hst ht.2 hfinite
  have hup := liftedQuadraticLengthOn_eq_integral_of_lipschitz R q hp (c 0) (c 1) δ s t
    hs.1 hst ht.2 ⟨K, hK⟩
  have hlength : phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t =
      phiLengthOn (q : X → ℂ → ℂ) γ s t := hup.trans hdown.symm
  have hprojection := quadraticDistance_le_actualLiftedDistance R q hp (δ.extend s) (δ.extend t)
  rw [hmap s, hmap t] at hprojection
  obtain ⟨β, _, hβ⟩ :=
    s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) δ hs.1 hst ht.2
  apply le_antisymm
  · calc phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t
        = phiLengthOn (q : X → ℂ → ℂ) γ s t := hlength
      _ = phiDistRS (q : X → ℂ → ℂ) (γ.extend s) (γ.extend t) := hseg
      _ ≤ phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (δ.extend s) (δ.extend t) := hprojection
  · exact le_trans
      (iInf_le (fun η : Path (δ.extend s) (δ.extend t) =>
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) η) β) hβ

end LowDimensionalTopology.Geometry.Teichmuller
