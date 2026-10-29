/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMobiusAction
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.LimitSets
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Fixed endpoints of conjugate lifted actions

Actual covering freeness excludes elliptic elements. Parabolic forward orbits
and loxodromic forward or backward orbits then approach every fixed endpoint.
Continuity of the given homeomorphic extensions transports those limits.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

private theorem extension_conjugacy_eq_of_orbit_limit
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {F₁ F₂ : ℍ ≃ₜ ℍ} {G₁ G₂ : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane}
    (hG₁ : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC F₁)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G₁)
    (hG₂ : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC F₂)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G₂)
    {N : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hconj : ∀ γ ∈ Γ, ∀ τ : ℍ,
      F₁ (γ • F₁.symm τ) = N • F₂ (γ • F₂.symm (N⁻¹ • τ)))
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Γ)
    {ξ : LiZhongQC.ExtPlane}
    (hlim : ∀ τ : ℍ, Tendsto
      (fun n : ℕ => (((δ ^ n • τ : ℍ) : ℂ) : LiZhongQC.ExtPlane)) atTop (𝓝 ξ)) :
    G₁ ξ = LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex N) (G₂ ξ) := by
  let Φ : ℍ → ℍ := fun τ => F₁.symm (N • F₂ τ)
  have hΦ (τ : ℍ) : F₁ (Φ τ) = N • F₂ τ := F₁.apply_symm_apply _
  have hcomm (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ) (τ : ℍ) :
      Φ (γ • τ) = γ • Φ τ := by
    have h := hconj γ hγ (N • F₂ τ)
    rw [inv_smul_smul, F₂.symm_apply_apply] at h
    exact (congrArg F₁.symm h).symm.trans (F₁.symm_apply_apply _)
  let u : ℕ → ℍ := fun n => δ ^ n • UpperHalfPlane.I
  have hu : Tendsto (fun n => (((u n : ℍ) : ℂ) : LiZhongQC.ExtPlane)) atTop (𝓝 ξ) :=
    hlim UpperHalfPlane.I
  have hξ : ξ ∈ closure (LiZhongQC.toExt LiZhongQC.upperHalf) :=
    isClosed_closure.mem_of_tendsto hu (Eventually.of_forall fun n =>
      subset_closure ⟨_, (u n).coe_im_pos, rfl⟩)
  have hΦu : Tendsto (fun n => (((Φ (u n) : ℍ) : ℂ) : LiZhongQC.ExtPlane))
      atTop (𝓝 ξ) := by
    apply (hlim (Φ UpperHalfPlane.I)).congr
    intro n
    exact congrArg (fun τ : ℍ => ((τ : ℂ) : LiZhongQC.ExtPlane))
      (hcomm (δ ^ n) (Γ.pow_mem hδ n) UpperHalfPlane.I).symm
  exact LiZhongQC.s27l_ext_eq_of_seq hG₂ hG₁ hΦ hξ hu hΦu

/-- Conjugacy of the actual lifted deck actions transports every fixed endpoint
through the given extensions. This includes parabolic points and infinity, and
requires neither compactness nor an independently supplied orbit limit. -/
theorem normalizedLift_conjugacy_fixed_endpoint
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    {F₁ F₂ : ℍ ≃ₜ ℍ} {G₁ G₂ : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane}
    (hG₁ : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC F₁)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G₁)
    (hG₂ : LiZhongQC.IsHomeoExtension (LiZhongQC.liftToC F₂)
      LiZhongQC.upperHalf LiZhongQC.upperHalf G₂)
    {N : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hconj : ∀ γ ∈ Γ, ∀ τ : ℍ,
      F₁ (γ • F₁.symm τ) = N • F₂ (γ • F₂.symm (N⁻¹ • τ)))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγΓ : γ ∈ Γ)
    (hγ : Hyperbolic.realSLMobius γ ≠ 1) {ξ : LiZhongQC.ExtPlane}
    (hsourcefix : LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) ξ = ξ) :
    G₁ ξ = LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex N) (G₂ ξ) := by
  have hfix : (Hyperbolic.realSLMobius γ).val ξ = ξ :=
    (congrFun (realSLMobius_source_action γ) ξ).trans hsourcefix
  have hnofix (τ : ℍ) :
      (Hyperbolic.realSLMobius γ).val ((τ : ℂ) : LiZhongQC.ExtPlane) ≠
        ((τ : ℂ) : LiZhongQC.ExtPlane) := by
    intro he
    have hτ : γ • τ = τ := UpperHalfPlane.ext (OnePoint.coe_injective
      ((Hyperbolic.realSLMobius_action γ τ).symm.trans he))
    rcases LiZhongQC.s27g_actsFreely hp γ hγΓ τ hτ with h | h
    · exact hγ (by rw [h, map_one])
    · exact hγ (by rw [h, Hyperbolic.realSLMobius_neg, map_one])
  rcases Mobius.mobius_nonidentity_type_trichotomy (Hyperbolic.realSLMobius γ) hγ with
    hP | hL | hE
  · obtain ⟨a, ha, hlim⟩ :=
      Mobius.mobius_parabolic_iterates_tendsto (Hyperbolic.realSLMobius γ) hP
    obtain ⟨b, hb⟩ := hP.2
    have hξa : ξ = a := ((hb ξ).mp hfix).trans ((hb a).mp ha).symm
    subst ξ
    apply extension_conjugacy_eq_of_orbit_limit hG₁ hG₂ hconj hγΓ
    intro τ
    simpa only [← map_pow, Hyperbolic.realSLMobius_action] using
      hlim ((τ : ℂ) : LiZhongQC.ExtPlane)
  · obtain ⟨a, b, hab⟩ :=
      Mobius.mobius_loxodromic_attracting_repelling (Hyperbolic.realSLMobius γ) hL
    rcases (DiscreteGroups.mobius_attracting_repelling_fixed_iff
      (Hyperbolic.realSLMobius γ) hγ a b hab ξ).mp hfix with rfl | rfl
    · apply extension_conjugacy_eq_of_orbit_limit hG₁ hG₂ hconj hγΓ
      intro τ
      have hτb : ((τ : ℂ) : LiZhongQC.ExtPlane) ≠ b := by
        intro he
        exact hnofix τ (by rw [he]; exact hab.2.2.1)
      simpa only [← map_pow, Hyperbolic.realSLMobius_action] using
        hab.2.2.2.1 ((τ : ℂ) : LiZhongQC.ExtPlane) hτb
    · apply extension_conjugacy_eq_of_orbit_limit hG₁ hG₂ hconj (Γ.inv_mem hγΓ)
      intro τ
      have hτa : ((τ : ℂ) : LiZhongQC.ExtPlane) ≠ a := by
        intro he
        exact hnofix τ (by rw [he]; exact hab.2.1)
      simpa only [← map_inv, ← map_pow, Hyperbolic.realSLMobius_action] using
        hab.2.2.2.2 ((τ : ℂ) : LiZhongQC.ExtPlane) hτa
  · have htr := (Hyperbolic.realSLMobius_elliptic_iff γ hγ).mp hE
    rw [Matrix.trace_fin_two] at htr
    have hlt : |γ 0 0 + γ 1 1| < 2 := by
      nlinarith [sq_abs (γ 0 0 + γ 1 1), abs_nonneg (γ 0 0 + γ 1 1)]
    obtain ⟨τ, hτ⟩ := LiZhongQC.s27g_elliptic_fixed hlt
    exact False.elim (hnofix τ (by rw [Hyperbolic.realSLMobius_action, hτ]))

end LowDimensionalTopology.Geometry.Teichmuller
