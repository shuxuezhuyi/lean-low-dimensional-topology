/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through the
credited boundary-extension and normalized-lift APIs;
see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalFrickeComparisonLift
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import Mathlib.Data.Set.Finite.Basic

/-!
# Boundary normalization of the original canonical comparison lift

The actual forward and backward orbit limits fix the dynamically labelled
boundary points of an intertwining lift. A point in the upper half-plane
can avoid the two exceptional orbit points. Consequently the original
canonical systems force the lift to fix zero, one and infinity, without
an axis-alternation hypothesis or a change of generators.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation Hyperbolic Mobius

private theorem boundary_forward_limit
    (A D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (B : ℍ ≃ₜ ℍ)
    (G : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane)
    (hG : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC B)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G)
    (hAD : ∀ z : ℍ, B (A • z) = D • B z)
    {a b c d : LiZhongQC.ExtPlane}
    (ha : a ∈ closure (LiZhongQC.toExt LiZhongQC.upperHalf))
    (hA : ∀ w : LiZhongQC.ExtPlane, w ≠ b → Tendsto
      (fun k : ℕ => ((realSLMobius A ^ k : complexMobiusGroup) :
        Equiv.Perm LiZhongQC.ExtPlane) w) atTop (𝓝 a))
    (hD : ∀ w : LiZhongQC.ExtPlane, w ≠ d → Tendsto
      (fun k : ℕ => ((realSLMobius D ^ k : complexMobiusGroup) :
        Equiv.Perm LiZhongQC.ExtPlane) w) atTop (𝓝 c)) :
    G a = c := by
  let ι : ℍ → LiZhongQC.ExtPlane := fun z => ((z : ℂ) : LiZhongQC.ExtPlane)
  have hι : Function.Injective ι := by
    intro z w h
    apply UpperHalfPlane.ext
    exact OnePoint.coe_injective h
  have hbad₁ : (ι ⁻¹' {b}).Finite :=
    Set.Finite.preimage hι.injOn (Set.finite_singleton b)
  have hbad₂ : ((ι ∘ B) ⁻¹' {d}).Finite :=
    Set.Finite.preimage (hι.comp B.injective).injOn (Set.finite_singleton d)
  obtain ⟨z, hz⟩ := (hbad₁.union hbad₂).exists_notMem
  have hzb : ι z ≠ b := by
    intro h
    apply hz
    exact Or.inl (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using h)
  have hzd : ι (B z) ≠ d := by
    intro h
    apply hz
    exact Or.inr (by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply] using h)
  have hseq (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) :
      (fun k : ℕ => ((realSLMobius M ^ k : complexMobiusGroup) :
        Equiv.Perm LiZhongQC.ExtPlane) (ι w)) =
      fun k : ℕ => ι (M ^ k • w) := by
    funext k
    change (realSLMobius M ^ k).val (w : ℂ) = (((M ^ k • w : ℍ) : ℂ) : ExtendedComplex)
    rw [← map_pow realSLMobius M k, realSLMobius_action]
  have hAlim := hA (ι z) hzb
  have hDlim := hD (ι (B z)) hzd
  rw [hseq A z] at hAlim
  rw [hseq D (B z)] at hDlim
  have hwithin : Tendsto (fun k : ℕ => ι (A ^ k • z)) atTop
      (𝓝[closure (LiZhongQC.toExt LiZhongQC.upperHalf)] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hAlim, Eventually.of_forall fun k => ?_⟩
    apply subset_closure
    exact ⟨((A ^ k • z : ℍ) : ℂ), (A ^ k • z).coe_im_pos, rfl⟩
  have hGlim := (hG.2.1 a ha).tendsto.comp hwithin
  have hpow (k : ℕ) : B (A ^ k • z) = D ^ k • B z := by
    induction k with
    | zero => simp
    | succ k ih => simp only [pow_succ', mul_smul, hAD, ih]
  have hvalues : (fun k : ℕ => G (ι (A ^ k • z))) =
      fun k : ℕ => ι (D ^ k • B z) := by
    funext k
    dsimp only [ι]
    rw [LiZhongQC.h36t_ext_coe hG, hpow k]
  change Tendsto (fun k : ℕ => G (ι (A ^ k • z))) atTop (𝓝 (G a)) at hGlim
  rw [hvalues] at hGlim
  exact tendsto_nhds_unique hGlim hDlim

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m n : MarkedRiemannSurface.{0, 0} R}

/-- The original dynamic labels force all three boundary values of the
actual intertwining comparison lift, without an alternation premise. -/
theorem NormalizedCanonicalFuchsianModel.comparison_boundary_normalized
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (B : ℍ ≃ₜ ℍ) {G : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane}
    (hG : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC B)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G)
    (hintertwine : ∀ (d : Edge g) (z : ℍ), B (P.matrices d • z) = Q.matrices d • B z) :
    G ((0 : ℂ) : LiZhongQC.ExtPlane) = ((0 : ℂ) : LiZhongQC.ExtPlane) ∧
      G ((1 : ℂ) : LiZhongQC.ExtPlane) = ((1 : ℂ) : LiZhongQC.ExtPlane) ∧
      G LiZhongQC.extInf = LiZhongQC.extInf := by
  obtain ⟨hc0, hc1, hcinf⟩ := LiZhongQC.s27l_mem_closure_01inf
  have hβ (z : ℍ) := hintertwine (finalHandle hg, 1) z
  have hinf := boundary_forward_limit
    (P.matrices (finalHandle hg, 1)) (Q.matrices (finalHandle hg, 1)) B G hG hβ hcinf
    P.beta_attracting_repelling.2.2.2.1 Q.beta_attracting_repelling.2.2.2.1
  have hβinv (z : ℍ) : B ((P.matrices (finalHandle hg, 1))⁻¹ • z) =
      (Q.matrices (finalHandle hg, 1))⁻¹ • B z := by
    apply eq_inv_smul_iff.mpr
    have h := hβ ((P.matrices (finalHandle hg, 1))⁻¹ • z)
    rw [smul_inv_smul] at h
    exact h.symm
  have h0 := boundary_forward_limit
    (P.matrices (finalHandle hg, 1))⁻¹ (Q.matrices (finalHandle hg, 1))⁻¹ B G hG hβinv hc0
    (by simpa only [map_inv] using P.beta_attracting_repelling.2.2.2.2)
    (by simpa only [map_inv] using Q.beta_attracting_repelling.2.2.2.2)
  obtain ⟨rP, hPα⟩ := P.alpha_attracting
  obtain ⟨rQ, hQα⟩ := Q.alpha_attracting
  have h1 := boundary_forward_limit
    (P.matrices (finalHandle hg, 0)) (Q.matrices (finalHandle hg, 0)) B G hG
    (hintertwine (finalHandle hg, 0)) hc1 hPα.2.2.2.1 hQα.2.2.2.1
  exact ⟨h0, h1, hinf⟩

/-- Every actual comparison in the prescribed free marking class has a
same-distortion lift with the original three-point normalization. -/
theorem NormalizedCanonicalFuchsianModel.exists_normalized_comparison_lift
    (P : NormalizedCanonicalFuchsianModel hg e m)
    (Q : NormalizedCanonicalFuchsianModel hg e n)
    (h : m.carrier ≃ₜ n.carrier) {K : ℝ} :
    let := m.surface.toRiemannAtlas.toChartedSpace
    let := n.surface.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsKQCRS h K →
      ContinuousMap.Homotopic
        ((_root_.toContinuousMap h).comp m.markingMap) n.markingMap →
      ∃ (B : ℍ ≃ₜ ℍ) (G : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane),
        LiZhongQC.IsNormalizedLift P.model.halfPlaneCover Q.model.halfPlaneCover h B G ∧
        LiZhongQC.IsKQC (LiZhongQC.liftToC B) LiZhongQC.upperHalf K ∧
        ∀ (d : Edge g) (z : ℍ), B (P.matrices d • z) = Q.matrices d • B z := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := n.surface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro hK hhom
  obtain ⟨B, hBlift, hBK, hintertwine⟩ := P.exists_comparison_lift Q h hK hhom
  obtain ⟨G, hG⟩ := LiZhongQC.thm13_3_boundary_correspondence
    LiZhongQC.isJordanDomain_upperHalf LiZhongQC.isJordanDomain_upperHalf
    ⟨K, hBK⟩ (LiZhongQC.h36q_liftToC_image B)
  obtain ⟨h0, h1, hinf⟩ := P.comparison_boundary_normalized Q B hG hintertwine
  exact ⟨B, G, ⟨hBlift, hG, h0, h1, hinf⟩, hBK, hintertwine⟩

end LowDimensionalTopology.Geometry.Teichmuller
