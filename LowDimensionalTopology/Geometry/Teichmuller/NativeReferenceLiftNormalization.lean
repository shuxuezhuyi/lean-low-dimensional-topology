module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaSourceRealization
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientMap
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedLiftDeckActions

/-!
# Normalize any given quasiconformal lift by an actual real Möbius map

The reference map and both of its original covering projections are supplied,
and the lift is the given lift. The coefficient is the original lifted
coefficient of that reference map, in its genuine native L-infinity class.
The normalized symmetric solution differs from that given lift by an actual
real Möbius transformation. The target covering is adjusted by the inverse
of that same transformation. No target subgroup equality modulo matrix sign
is replaced by a raw SL subgroup equality.

The uniformization and lift arguments reuse Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

/-- Taking the native a.e. class preserves the actual normalized symmetric solution. -/
theorem normalizedMap_fromSourceGamma {Γ : Subgroup Deck} (μ : LiZhongQC.BeltramiGamma Γ) :
    normalizedMap (fromSourceGamma μ) = LiZhongQC.fMuSym μ.val.val := by
  let ν := fromSourceGamma μ
  obtain ⟨k, hk0, hk1, hμ⟩ := LiZhongQC.bg_beltramiH_upper μ.val
  have hn : ‖ν.val.val‖ < 1 := by
    rw [ClosedSubmodule.norm_coe]
    exact Ball.norm_lt_one ν
  have he := LiZhongQC.s27u_fSym_congr_ae
    (norm_nonneg ν.val.val) hn (planeRepresentative_isBeltramiCoeff ν.val.val)
    hk0 hk1 hμ (toSourceGamma_fromSourceGamma_ae μ)
  change LiZhongQC.fMuSym (planeRepresentative ν.val.val) = LiZhongQC.fMuSym μ.val.val
  simpa only [LiZhongQC.s33v_fSym_eq] using he

universe u
variable {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- Any actual given lift differs from the genuine normalized coefficient solution
by one actual real Möbius map. Both original projections and the exact original
reference marking remain attached to this statement. -/
theorem exists_native_normalization_of_given_lift
    {Γ Γ1 : Subgroup Deck} {p : ℍ → X} {p1 : ℍ → Y}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (f : X ≃ₜ Y) (hf : LiZhongQC.IsQCRS f) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) :
    ∃ (ν : Ball Γ) (M : Deck),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p f) ∧
      (∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) ∧
      LiZhongQC.IsUniformization (LiZhongQC.conjGroup Γ1 M)
        (LiZhongQC.adjustProjection p1 M) := by
  obtain ⟨μ, hμ, hcompat⟩ := LiZhongQC.s27u_liftCoeff_beltramiH hp hf
  let ρ : LiZhongQC.BeltramiGamma Γ := ⟨μ, hcompat⟩
  let ν : Ball Γ := fromSourceGamma ρ
  obtain ⟨F, hF, hU, _, _, _⟩ := LiZhongQC.s27u_uniformization_transport hp f hf
  have hΦ : LiZhongQC.IsLift p1 (LiZhongQC.s27u_proj p f F)
      (Homeomorph.refl Y) (w.symm.trans F) := by
    intro τ
    change f (p (F.symm (F (w.symm τ)))) = p1 τ
    rw [F.symm_apply_apply, ← hw (w.symm τ), w.apply_symm_apply]
  have hid : LiZhongQC.IsKQCRS (Homeomorph.refl Y) 1 :=
    (LiZhongQC.isKQCRS_one_iff _).mpr LiZhongQC.isBiholomorphic_id
  obtain ⟨M, hM⟩ := LiZhongQC.utm_eq_smul_of_isKQC_one (w.symm.trans F)
    (LiZhongQC.h23l_lift_isKQC hp1 hU hid hΦ)
  have hnative : ∀ τ : ℍ, normalizedUpperEquiv ν τ = F τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [normalizedUpperEquiv_coe, normalizedMap_fromSourceGamma]
    change LiZhongQC.fMuSym μ.val τ = (F τ : ℂ)
    rw [← LiZhongQC.s33v_fSym_eq, hμ]
    exact (hF τ).symm
  refine ⟨ν, M, ?_, ?_, LiZhongQC.adjustProjection_isUniformization hp1 M⟩
  · filter_upwards [toSourceGamma_fromSourceGamma_ae ρ] with z hz
    exact hz.trans (congrFun hμ z)
  · intro τ
    rw [hnative]
    have he := hM (w τ)
    simpa only [Homeomorph.trans_apply, w.symm_apply_apply] using he

private theorem deformedGroup_upper_forward {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) {γ : Deck} (hγ : γ ∈ Γ) :
    ∃ δ ∈ deformedGroup hΓ ν, ∀ τ : ℍ,
      normalizedUpperEquiv ν (γ • τ) = δ • normalizedUpperEquiv ν τ := by
  obtain ⟨δ, hδ, he⟩ := (deformedGroup_spec hΓ ν).2.1 γ hγ
  refine ⟨δ, hδ, fun τ => ?_⟩
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
    LiZhongQC.mobiusFn] using he (τ : ℂ) τ.im_pos

private theorem deformedGroup_upper_backward {Γ : Subgroup Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) {δ : Deck} (hδ : δ ∈ deformedGroup hΓ ν) :
    ∃ γ ∈ Γ, ∀ τ : ℍ,
      normalizedUpperEquiv ν (γ • τ) = δ • normalizedUpperEquiv ν τ := by
  obtain ⟨γ, hγ, he⟩ := (deformedGroup_spec hΓ ν).2.2 δ hδ
  refine ⟨γ, hγ, fun τ => ?_⟩
  apply UpperHalfPlane.ext
  simpa only [normalizedUpperEquiv_coe, LiZhongQC.h23l_b_coe_smul,
    LiZhongQC.mobiusFn] using he (τ : ℂ) τ.im_pos

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- The actual normalized deformed group and adjusted given target group have
exactly the same actions. Their determinant-one representatives may differ by sign. -/
theorem normalized_given_lift_deck_actions
    {Γ Γ1 : Subgroup Deck} {p : ℍ → X} {p1 : ℍ → Y}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (w : ℍ ≃ₜ ℍ)
    (hw : LiZhongQC.IsLift p p1 f w) (ν : Ball Γ) (M : Deck)
    (hM : ∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) :
    (∀ γ ∈ deformedGroup hΓ ν, ∃ δ ∈ LiZhongQC.conjGroup Γ1 M,
      ∀ τ : ℍ, γ • τ = δ • τ) ∧
    (∀ δ ∈ LiZhongQC.conjGroup Γ1 M, ∃ γ ∈ deformedGroup hΓ ν,
      ∀ τ : ℍ, δ • τ = γ • τ) := by
  constructor
  · intro γ hγ
    obtain ⟨a, ha, hN⟩ := deformedGroup_upper_backward hΓ ν hγ
    obtain ⟨b, hb, hwab⟩ := LiZhongQC.h23l_deck hp hp1 hw ha
    have hbM : M * b * M⁻¹ ∈ LiZhongQC.conjGroup Γ1 M := by
      change M * b * M⁻¹ ∈ Γ1.map (MulAut.conj M).toMonoidHom
      exact ⟨b, hb, rfl⟩
    refine ⟨M * b * M⁻¹, hbM, ?_⟩
    intro τ
    obtain ⟨z, rfl⟩ := (normalizedUpperEquiv ν).surjective τ
    calc
      γ • normalizedUpperEquiv ν z = normalizedUpperEquiv ν (a • z) := (hN z).symm
      _ = M • w (a • z) := hM (a • z)
      _ = M • (b • w z) := congrArg (fun t : ℍ => M • t) (hwab z)
      _ = (M * b * M⁻¹) • normalizedUpperEquiv ν z := by
        rw [hM z, mul_smul, mul_smul, inv_smul_smul]
  · intro δ hδ
    change δ ∈ Γ1.map (MulAut.conj M).toMonoidHom at hδ
    obtain ⟨b, hb, hbδ⟩ := hδ
    have hδeq : δ = M * b * M⁻¹ := by
      rw [← hbδ]
      rfl
    have hwi : LiZhongQC.IsLift p1 p f.symm w.symm := by
      intro τ
      have he := congrArg f.symm (hw (w.symm τ))
      simpa only [w.apply_symm_apply, f.symm_apply_apply] using he.symm
    obtain ⟨a, ha, hwa⟩ := LiZhongQC.h23l_deck hp1 hp hwi hb
    obtain ⟨γ, hγ, hN⟩ := deformedGroup_upper_forward hΓ ν ha
    refine ⟨γ, hγ, ?_⟩
    intro τ
    obtain ⟨z, rfl⟩ := (normalizedUpperEquiv ν).surjective τ
    have hwab : w (a • z) = b • w z := by
      have he := congrArg w (hwa (w z))
      simpa only [w.apply_symm_apply, w.symm_apply_apply] using he.symm
    calc
      δ • normalizedUpperEquiv ν z = (M * b * M⁻¹) • (M • w z) := by rw [hδeq, hM z]
      _ = M • (b • w z) := by rw [mul_smul, mul_smul, inv_smul_smul]
      _ = M • w (a • z) := congrArg (fun t : ℍ => M • t) hwab.symm
      _ = normalizedUpperEquiv ν (a • z) := (hM (a • z)).symm
      _ = γ • normalizedUpperEquiv ν z := hN z

/-- No identification of the arbitrary given target group is assumed: the
coefficient, real normalization, adjusted target cover and both directions
of actual deck-action correspondence are all derived from the given lift. -/
theorem exists_native_given_lift_and_deck_actions
    {Γ Γ1 : Subgroup Deck} {p : ℍ → X} {p1 : ℍ → Y}
    (hp : LiZhongQC.IsUniformization Γ p) (hp1 : LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : X ≃ₜ Y) (hf : LiZhongQC.IsQCRS f)
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 f w) :
    ∃ (ν : Ball Γ) (M : Deck),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p f) ∧
      (∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) ∧
      LiZhongQC.IsUniformization (LiZhongQC.conjGroup Γ1 M)
        (LiZhongQC.adjustProjection p1 M) ∧
      (∀ γ ∈ deformedGroup hΓ ν, ∃ δ ∈ LiZhongQC.conjGroup Γ1 M,
        ∀ τ : ℍ, γ • τ = δ • τ) ∧
      (∀ δ ∈ LiZhongQC.conjGroup Γ1 M, ∃ γ ∈ deformedGroup hΓ ν,
        ∀ τ : ℍ, δ • τ = γ • τ) := by
  obtain ⟨ν, M, hν, hM, hpM⟩ := exists_native_normalization_of_given_lift hp hp1 f hf w hw
  exact ⟨ν, M, hν, hM, hpM, normalized_given_lift_deck_actions hp hp1 hΓ f w hw ν M hM⟩

/-- The original native closed surfaces supply their actual complete atlases.
Thus no additional chosen-atlas or target-group identification premise is
needed to apply the given-lift normalization and deck-action theorem. -/
theorem exists_original_reference_lift_normalization
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (R : Surfaces.ClosedRiemannSurface A) (R1 : Surfaces.ClosedRiemannSurface B)
    {Γ Γ1 : Subgroup Deck} {p : ℍ → A} {p1 : ℍ → B}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hp1 : let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ1 p1)
    (hΓ : LiZhongQC.IsFuchsian Γ) (f : A ≃ₜ B)
    (hf : let := R.toRiemannAtlas.toChartedSpace
      let := R1.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS f)
    (w : ℍ ≃ₜ ℍ) (hw : LiZhongQC.IsLift p p1 f w) :
    let := R1.toRiemannAtlas.toChartedSpace
    ∃ (ν : Ball Γ) (M : Deck),
      (planeRepresentative ν.val.val =ᵐ[volume.restrict LiZhongQC.upperHalf]
        LiZhongQC.s27u_liftCoeff p f) ∧
      (∀ τ : ℍ, normalizedUpperEquiv ν τ = M • w τ) ∧
      LiZhongQC.IsUniformization (LiZhongQC.conjGroup Γ1 M)
        (LiZhongQC.adjustProjection p1 M) ∧
      (∀ γ ∈ deformedGroup hΓ ν, ∃ δ ∈ LiZhongQC.conjGroup Γ1 M,
        ∀ τ : ℍ, γ • τ = δ • τ) ∧
      (∀ δ ∈ LiZhongQC.conjGroup Γ1 M, ∃ γ ∈ deformedGroup hΓ ν,
        ∀ τ : ℍ, δ • τ = γ • τ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R1.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R1.toRiemannAtlas.isManifold
  exact exists_native_given_lift_and_deck_actions hp hp1 hΓ f hf w hw

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
