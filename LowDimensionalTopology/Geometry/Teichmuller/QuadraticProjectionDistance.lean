/-
The finite-partition Lipschitz gluing is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedQuadraticIntervalLength
public import Mathlib.Topology.UnitInterval

/-!
# Quadratic distance under the actual uniformizing projection

The projection of an admissible native upper-half-plane path has an actual
finite chart subdivision with the same coefficient integral. Its native length
therefore does not increase, and taking the original path infima gives the
distance inequality for the same lifted quadratic differential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- Finite native quadratic length in the standard upper-half-plane atlas
supplies a global Lipschitz bound in the actual complex coordinate. -/
theorem nativeH_lipschitz_of_length_lt_top
    (qH : UpperHalfPlane → ℂ → ℂ) {a b : UpperHalfPlane} (δ : Path a b) :
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    phiLengthPath qH δ < ⊤ →
      ∃ K : ℝ≥0, LipschitzOnWith K (fun u : ℝ => (δ.extend u : ℂ)) (Icc 0 1) := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  intro hfinite
  have hchart (x : UpperHalfPlane) : chartAt ℂ x = UpperHalfPlane.ofComplex.symm := by
    have hx := chart_mem_atlas ℂ x
    change chartAt ℂ x ∈ ({UpperHalfPlane.ofComplex.symm} :
      Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at hx
    exact Set.mem_singleton_iff.mp hx
  have hcoord (x : UpperHalfPlane) :
      (fun u : ℝ => chartAt ℂ x (δ.extend u)) = (fun u : ℝ => (δ.extend u : ℂ)) := by
    funext u
    rw [hchart x]
    rfl
  unfold phiLengthPath phiLengthOn at hfinite
  simp only [iInf_lt_iff] at hfinite
  obtain ⟨n, τ, x, hP, _⟩ := hfinite
  have hloc : ∀ i : Fin n, ∃ K : ℝ≥0, LipschitzOnWith K
      (fun u : ℝ => (δ.extend u : ℂ)) (Icc (τ i.castSucc) (τ i.succ)) := by
    intro i
    obtain ⟨K, hK⟩ := (hP.2.2.2 i).2
    rw [hcoord (x i)] at hK
    exact ⟨K, hK⟩
  choose K hK using hloc
  have hpiece : ∀ i : Fin n, LipschitzOnWith (Finset.univ.sup K)
      (fun u : ℝ => (δ.extend u : ℂ)) (Icc (τ i.castSucc) (τ i.succ)) := fun i =>
    (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  have hall : ∀ j : Fin (n + 1), LipschitzOnWith (Finset.univ.sup K)
      (fun u : ℝ => (δ.extend u : ℂ)) (Icc (τ 0) (τ j)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro s hs t ht
      have hst : s = t := le_antisymm (hs.2.trans ht.1) (ht.2.trans hs.1)
      rw [hst, edist_self]
      exact zero_le
    | succ i ih => exact utm_a_lipschitzOnWith_Icc_union ih (hpiece i)
  refine ⟨Finset.univ.sup K, ?_⟩
  have h := hall (Fin.last n)
  rwa [hP.1, hP.2.1] at h

/-- The actual projection does not increase the length of a supplied lifted path. -/
theorem actualUniformizingProjection_pathLength_le
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (δ : Path a b),
        phiLengthPath (q : X → ℂ → ℂ) (δ.map hp.1.continuous) ≤
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ
  by_cases htop : phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨K, hK⟩ := nativeH_lipschitz_of_length_lt_top
    (qH : UpperHalfPlane → ℂ → ℂ) δ (lt_top_iff_ne_top.mpr htop)
  let α : Path (p a) (p b) := δ.map hp.1.continuous
  have hc : ∀ u, p (δ.toContinuousMap u) = α u := fun _ => rfl
  have hpext (u : ℝ) : utm_pext p (δ.extend u : ℂ) = α.extend u :=
    utm_a_pext_lift α δ.toContinuousMap hc u
  have hlocal : ∀ z : UpperHalfPlane, ∃ (V : Set ℂ) (L : ℝ≥0),
      IsOpen V ∧ (z : ℂ) ∈ V ∧
      (∀ w ∈ V, utm_pext p w ∈ (chartAt ℂ (p z)).source) ∧
      LipschitzOnWith L (fun w => chartAt ℂ (p z) (utm_pext p w)) V := by
    intro z
    obtain ⟨U, hUo, hzU, _, _, hU⟩ :=
      utm_liftQD_local q.property hp z (p z) (mem_chart_source ℂ (p z))
    have hdiffU : DifferentiableOn ℂ (fun w => chartAt ℂ (p z) (utm_pext p w)) U :=
      fun w hw => (hU w hw).2.1.differentiableAt.differentiableWithinAt
    have hs := (hdiffU.analyticAt (hUo.mem_nhds hzU)).hasStrictDerivAt
    obtain ⟨L, N, hN, hLN⟩ := hs.hasStrictFDerivAt.exists_lipschitzOnWith
    obtain ⟨V, hV, hVo, hzV⟩ := mem_nhds_iff.mp (inter_mem (hUo.mem_nhds hzU) hN)
    refine ⟨V, L, hVo, hzV, ?_, hLN.mono fun w hw => (hV hw).2⟩
    exact fun w hw => (hU w (hV hw).1).1
  choose V L hVo hzV hVsrc hVLip using hlocal
  let C : UpperHalfPlane → Set unitInterval := fun z => {u | (δ u : ℂ) ∈ V z}
  have hC : ∀ z, IsOpen (C z) := fun z =>
    (hVo z).preimage (UpperHalfPlane.continuous_coe.comp δ.continuous)
  have hcover : (univ : Set unitInterval) ⊆ ⋃ z, C z := by
    intro u _
    exact mem_iUnion.mpr ⟨δ u, hzV (δ u)⟩
  obtain ⟨σ, hσ0, hσ, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hC hcover
  let N : ℕ := m + 1
  let τ : Fin (N + 1) → ℝ := fun j => (σ j.val : ℝ)
  have hτ0 : τ 0 = 0 := by simp [τ, hσ0]
  have hτ1 : τ (Fin.last N) = 1 := by
    have h := congrArg (fun u : unitInterval => (u : ℝ)) (hm (m + 1) (Nat.le_succ m))
    simpa [τ, N] using h
  have hτ : Monotone τ := by
    intro i j hij
    exact hσ (show i.val ≤ j.val from hij)
  have hτI (j : Fin (N + 1)) : τ j ∈ Icc (0 : ℝ) 1 := (σ j.val).property
  have hIcc (i : Fin N) : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc (0 : ℝ) 1 :=
    fun _ hu => ⟨(hτI i.castSucc).1.trans hu.1, hu.2.trans (hτI i.succ).2⟩
  have hpieces : ∀ i : Fin N, ∃ z : UpperHalfPlane,
      ∀ u ∈ Icc (τ i.castSucc) (τ i.succ), (δ.extend u : ℂ) ∈ V z := by
    intro i
    obtain ⟨z, hz⟩ := hsub i.val
    refine ⟨z, ?_⟩
    intro u hu
    have huI := hIcc i hu
    have ht : (⟨u, huI⟩ : unitInterval) ∈ Icc (σ i.val) (σ (i.val + 1)) := hu
    have hmem := hz ht
    change (δ (⟨u, huI⟩ : unitInterval) : ℂ) ∈ V z at hmem
    rw [Path.extend_apply δ huI]
    exact hmem
  choose z hz using hpieces
  let x : Fin N → X := fun i => p (z i)
  have hP : τ 0 = 0 ∧ τ (Fin.last N) = 1 ∧ Monotone τ ∧
      ∀ i : Fin N,
        α.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
          ∃ B : ℝ≥0, LipschitzOnWith B (fun u : ℝ => chartAt ℂ (x i) (α.extend u))
            (Icc (τ i.castSucc) (τ i.succ)) := by
    refine ⟨hτ0, hτ1, hτ, fun i => ⟨?_, L (z i) * K, ?_⟩⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [← hpext u]
      exact hVsrc (z i) _ (hz i u hu)
    · have hcomp := (hVLip (z i)).comp (hK.mono (hIcc i)) (hz i)
      intro u hu v hv
      change edist (chartAt ℂ (p (z i)) (α.extend u))
        (chartAt ℂ (p (z i)) (α.extend v)) ≤ _
      rw [← hpext u, ← hpext v]
      exact hcomp hu hv
  let F : ℝ → ℝ≥0∞ := fun u =>
    phiDensity ψ (δ.extend u : ℂ) * ‖deriv (fun v : ℝ => (δ.extend v : ℂ)) u‖ₑ
  have hsum :
      (∑ i : Fin N, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity ((q : X → ℂ → ℂ) (x i)) (chartAt ℂ (x i) (α.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x i) (α.extend v)) u‖ₑ) =
        ∫⁻ u in Ioo (0 : ℝ) 1, F u := by
    have hE := utm_a_lintegral_sum_eq F N τ hτ
    rw [hτ0, hτ1] at hE
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hE
    refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    exact utm_a_density_speed q.property hp α δ.toContinuousMap hc (x i)
      ((hP.2.2.2 i).1 ⟨u, Ioo_subset_Icc_self hu, rfl⟩)
  have hnative : phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ =
      ∫⁻ u in Ioo (0 : ℝ) 1, F u :=
    liftedQuadraticLengthOn_eq_integral_of_lipschitz R q hp a b δ 0 1
      le_rfl zero_lt_one le_rfl ⟨K, hK⟩
  rw [hnative]
  change phiLengthOn (q : X → ℂ → ℂ) α 0 1 ≤ ∫⁻ u in Ioo (0 : ℝ) 1, F u
  unfold phiLengthOn
  exact iInf_le_of_le N (iInf_le_of_le τ (iInf_le_of_le x (iInf_le_of_le hP hsum.le)))


/-- The actual uniformizing projection does not increase the original quadratic
distance, with the native upper-half-plane distance of its same pullback. -/
theorem quadraticDistance_le_actualLiftedDistance
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ a b : UpperHalfPlane,
        phiDistRS (q : X → ℂ → ℂ) (p a) (p b) ≤
          phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) a b := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b

  unfold phiDistRS
  refine le_iInf fun δ => ?_
  exact le_trans
    (iInf_le (fun γ : Path (p a) (p b) => phiLengthPath (q : X → ℂ → ℂ) γ)
      (δ.map hp.1.continuous)) (actualUniformizingProjection_pathLength_le R q hp δ)

end LowDimensionalTopology.Geometry.Teichmuller
