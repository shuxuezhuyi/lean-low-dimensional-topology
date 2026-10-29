module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularOneSupportFromActualFibers
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
public import LowDimensionalTopology.Unproved.Teichmuller.QuasiconformalSmoothing

/-!
# The full original cuff in a prescribed covering of the same actual target

An identity lift compares the model cover and the prescribed actual cover.
It is a real Mobius map. The original full-period canonical fibers therefore
transfer to the actual target cover, and the given oriented free homotopy
transfers the same full generator to the marked loop. No geodesic
parametrization of that marked loop or new hyperbolic model is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane unitInterval

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open Surfaces Hyperbolic

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem canonical_fibers_conjugated
    {X : Type} (p₀ p : ℍ → X) (A B T : Deck)
    (hprojection : ∀ z : ℍ, p (T • z) = p₀ z)
    (hB : realSLMobius (T * A * T⁻¹) = realSLMobius B)
    (hfib : ∀ z ∈ hCanonicalRegion A, ∀ w ∈ hCanonicalRegion A,
      p₀ z = p₀ w ↔ ∃ n : ℤ, w = A ^ n • z) :
    ∀ z ∈ hCanonicalRegion B, ∀ w ∈ hCanonicalRegion B,
      p z = p w ↔ ∃ n : ℤ, w = B ^ n • z := by
  have hregion : hCanonicalRegion B = (fun z : ℍ => T • z) '' hCanonicalRegion A :=
    (hCanonicalRegion_congr _ _ hB).symm.trans (hCanonicalRegion_conjugation A T)
  intro z hz w hw
  obtain ⟨z₀, hz₀, rfl⟩ := hregion ▸ hz
  obtain ⟨w₀, hw₀, rfl⟩ := hregion ▸ hw
  have hpower (n : ℤ) : B ^ n • (T • z₀) = T • (A ^ n • z₀) := by
    have he : realSLMobius (B ^ n) = realSLMobius (T * A ^ n * T⁻¹) := by
      rw [map_zpow, ← hB]
      simp only [map_mul, map_inv, map_zpow]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        (((MulAut.conj (realSLMobius T)).toMonoidHom).map_zpow
          (realSLMobius A) n).symm
    have h := congrArg (fun E : ℍ ≃ᵢ ℍ => E (T • z₀))
      (Fuchsian.hSLIsometry_eq_of_realSLMobius_eq _ _ he)
    change B ^ n • (T • z₀) = (T * A ^ n * T⁻¹) • (T • z₀) at h
    simpa only [mul_smul, inv_smul_smul] using h
  rw [hprojection, hprojection, hfib z₀ hz₀ w₀ hw₀]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg (fun z : ℍ => T • z) hn).trans (hpower n).symm⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, (MulAction.injective T) ?_⟩
    exact hn.trans (hpower n)

/-- An actual single-traversal original geodesic supplies its full oriented
normalization and one-support angular band in any prescribed uniformization
of the same target, for any loop in its given oriented free homotopy class. -/
theorem originalCuff_exists_normalization_for_prescribed_cover
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X))
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (α : LiZhongQC.Loop X) (hα : LiZhongQC.FreelyHomotopic α q.toLoop) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s)
      (_hA : realSLMobius A ≠ 1) (_ht : 4 < (Matrix.trace A.val) ^ 2),
      A ∈ Γ ∧ LiZhongQC.Covers p A α ∧
      realSLMobius (Q * A * Q⁻¹) = realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
      ∀ ζ : ℂ,
        ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s)),
          rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΓQ s u ζ ≠ 0 →
            rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΓQ s v ζ ≠ 0 →
              u = v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨Γ₀, _hΓ₀, hp₀⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨B, _hB0, _htB, hBΓ₀, hcovB, hsimple, hfibB⟩ :=
    q.exists_canonical_collar_fibers_of_circle_injective hp₀ hcircle
  obtain ⟨z₁, hz₁⟩ := hp.2.2.1 (M.halfPlaneCover UpperHalfPlane.I)
  obtain ⟨F, hF, _hFbase⟩ := LiZhongQC.exists_lift hp₀ hp
    (Homeomorph.refl X) UpperHalfPlane.I z₁ hz₁
  have hidentity : LiZhongQC.IsKQCRS (Homeomorph.refl X) 1 :=
    (LiZhongQC.isKQCRS_one_iff _).mpr LiZhongQC.isBiholomorphic_id
  obtain ⟨T, hT⟩ := LiZhongQC.utm_eq_smul_of_isKQC_one F
    (LiZhongQC.h23l_lift_isKQC hp₀ hp hidentity hF)
  have hprojection (z : ℍ) : p (T • z) = M.halfPlaneCover z := by
    rw [← hT z]
    exact hF z
  obtain ⟨E, hEΓ, hdeck⟩ := LiZhongQC.h23l_deck hp₀ hp hF hBΓ₀
  have haction (z : ℍ) : E • (T • z) = T • (B • z) := by
    have h := hdeck z
    rw [hT (B • z), hT z] at h
    exact h.symm
  have hE : realSLMobius (T * B * T⁻¹) = realSLMobius E := by
    apply realSLMobius_ext_action
    intro z
    simpa only [mul_smul, smul_inv_smul] using (haction (T⁻¹ • z)).symm
  have hfibE := canonical_fibers_conjugated M.halfPlaneCover p B E T
    hprojection hE hfibB
  have hcovE : LiZhongQC.Covers p E q.toLoop := by
    obtain ⟨c, hc, hcp, hperiod⟩ := hcovB
    refine ⟨fun t => T • c t, (continuous_const_smul T).comp_continuousOn hc, ?_, ?_⟩
    · intro t ht
      rw [hprojection]
      exact hcp t ht
    · change T • c 1 = E • (T • c 0)
      rw [hperiod]
      exact (haction (c 0)).symm
  have hEH : Mobius.MobiusHyperbolic (realSLMobius E) := by
    rw [← hE, map_mul, map_mul, map_inv]
    exact Mobius.mobiusHyperbolic_conjugation_forward _ _ hsimple.2.1
  obtain ⟨_B, _hB, c, hc, hcp, _hcperiod⟩ := LiZhongQC.s30a_exists_covers hp α
  let d : C(I, ℍ) :=
    ⟨fun u => c u, hc.comp_continuous continuous_subtype_val (fun u => u.property)⟩
  have hd (u : I) : p (d u) = α.2 u :=
    (hcp u u.property).trans (Path.extend_extends' α.2 u)
  obtain ⟨δ, hδΓ, hperiod⟩ :=
    LiZhongQC.s30a_fh_fwd hp hEΓ hcovE (LiZhongQC.s30b_fh_symm hα) d hd
  let A : Deck := δ * E * δ⁻¹
  have hAΓ : A ∈ Γ := Γ.mul_mem (Γ.mul_mem hδΓ hEΓ) (Γ.inv_mem hδΓ)
  have hcovA : LiZhongQC.Covers p A α := ⟨c, hc, hcp, hperiod⟩
  have hfibA := canonical_fibers_conjugated p p E A δ
    (fun z => LiZhongQC.s30a_p_smul hp hδΓ z) rfl hfibE
  have hAH : Mobius.MobiusHyperbolic (realSLMobius A) := by
    simpa only [A, map_mul, map_inv] using
      Mobius.mobiusHyperbolic_conjugation_forward (realSLMobius E) (realSLMobius δ) hEH
  have hA0 : realSLMobius A ≠ 1 := hAH.1.1
  have htA : 4 < (Matrix.trace A.val) ^ 2 := (realSLMobius_hyperbolic_iff A hA0).mp hAH
  obtain ⟨Q, s, hs, hQA⟩ := Fuchsian.realSLMobius_hyperbolic_positive_log_normal_form A hAH
  exact ⟨A, Q, s, hs, hA0, htA, hAΓ, hcovA, hQA,
    normalizedAngular_one_support_of_canonical_fibers hp A Q s hs hAΓ hQA hfibA⟩

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami
open NormalizedCoefficientTransport AngularTwist

/-- The existing marked-target pants family supplies an actual full cuff
and its oriented free class on every actual deformed reference. Its
normalization and one-support data use the prescribed deformed cover. -/
theorem originalFN_deformedReference_exists_normalization
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (ν : Ball Γ) (j : Fin (3 * g - 3)) :
    let Y := deformedNativeSurface R hgenus hΓ hp ν
    letI := Y.toRiemannAtlas.toChartedSpace
    let Δ := deformedGroup hΓ ν
    let pY := deformedTargetCover R hgenus hΓ hp ν
    let eY := deformedTargetMarking R hgenus hΓ hp ν
    let α : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
      ⟨eY (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map eY.continuous⟩
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s)
      (_hA : Hyperbolic.realSLMobius A ≠ 1) (_ht : 4 < (Matrix.trace A.val) ^ 2),
      A ∈ Δ ∧ LiZhongQC.Covers pY A α ∧
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΔQ := Δ.map (MulAut.conj Q).toMonoidHom
      ∀ ζ : ℂ,
        ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΔQ s)),
          rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΔQ s u ζ ≠ 0 →
            rightCosetInfinitesimalZeroExtension (canonicalBandWidth s hs) ΔQ s v ζ ≠ 0 →
              u = v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  let := Y.toRiemannAtlas.toChartedSpace
  let eY := deformedTargetMarking R hgenus hΓ hp ν
  obtain ⟨K, hqc⟩ := deformedTargetMarking_nativeQC R hp hgenus hΓ ν
  obtain ⟨F, hF, hhom, _hnorm⟩ := hsmooth R Y eY K hqc.1 hqc 1 zero_lt_one
  let m : MarkedRiemannSurface.{0, 0} R :=
    { carrier := (deformedTargetSource R hgenus hΓ hp ν).carrier
      topology := inferInstance
      surface := Y
      marking := F
      orientation_preserving := hF }
  obtain ⟨family, _hrepresentative, _hmodel, _hphase⟩ := hU
  let D := (family m).1
  let α : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
    ⟨eY (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map eY.continuous⟩
  have hmarked := LiZhongQC.s30b_fh_of_homotopic hhom (D₀.cuff j).toLoop
  have hα : LiZhongQC.FreelyHomotopic α (D.cuff j).toLoop :=
    LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hmarked)
      ((family m).2.cuff_orientation j)
  exact originalCuff_exists_normalization_for_prescribed_cover Y (D.cuff j) (D.simple j)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) α hα

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
