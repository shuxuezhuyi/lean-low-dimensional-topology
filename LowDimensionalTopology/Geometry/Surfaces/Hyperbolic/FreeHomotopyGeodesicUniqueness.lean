module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.EquivariantAxisUniqueness
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Free homotopy aligns the actual periods of closed geodesic lifts

The actual covering homotopy supplies a conjugate deck element. Uniqueness of
continuous lifts extends the endpoint equation to the complete geodesic.
Conjugating by that actual deck element then reduces to oriented axis
uniqueness, retaining every proper-power period.

The homotopy-lifting API is due to Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Deck isometries preserve genuine complete unit-speed geodesics. -/
private theorem isHGeodesicParam_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {δ : ℝ → ℍ}
    (hδ : IsHGeodesicParam δ) : IsHGeodesicParam (fun t => A • δ t) := by
  have his : Isometry (fun z : ℍ => A • z) := isometry_smul ℍ A
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hδ.2
  obtain ⟨M, hM⟩ := LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine his L
  refine ⟨his.comp hδ.1, ?_⟩
  have hrange : range (fun t => A • δ t) = M.carrier := by
    change range ((fun z : ℍ => A • z) ∘ δ) = M.carrier
    rw [range_comp, ← hL, hM]
  exact hrange.symm ▸ M.isHLine

/-- Actual freely homotopic closed loops with complete unit-speed geodesic
lifts have the same full period and the same projected parametrization up to
translation of the real parameter. Neither matrix is replaced by a primitive
generator. The existence of complete geodesic lifts is stated explicitly. -/
theorem freelyHomotopic_geodesic_lifts_unique_up_to_shift
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ) (hBΓ : B ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {γ δ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) (hδ : IsHGeodesicParam δ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hγperiod : ∀ t : ℝ, γ (t + T) = A • γ t)
    (hδperiod : ∀ t : ℝ, δ (t + U) = B • δ t)
    (α β : LiZhongQC.Loop S) (hcov : LiZhongQC.Covers p A α)
    (hfree : LiZhongQC.FreelyHomotopic α β)
    (hβ : ∀ t : I, β.2 t = p (δ (U * (t : ℝ)))) :
    T = U ∧ T = hTranslationLength (hSLIsometry A) ∧
      ∃ c : ℝ, ∀ t : ℝ, p (γ t) = p (δ (t + c)) := by
  let d : C(I, ℍ) := ⟨fun t => δ (U * (t : ℝ)),
    hδ.1.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
  have hd (t : I) : p (d t) = β.2 t := (hβ t).symm
  obtain ⟨C, hC, hend⟩ := LiZhongQC.s30a_fh_fwd hp hAΓ hcov hfree d hd
  let D := C * A * C⁻¹
  have hDΓ : D ∈ Γ := Γ.mul_mem (Γ.mul_mem hC hAΓ) (Γ.inv_mem hC)
  have hinit : δ (0 + U) = D • δ 0 := by
    change δ (U * 1) = D • δ (U * 0) at hend
    simpa only [mul_one, mul_zero, zero_add] using hend
  have hproject (t : ℝ) : p (δ (t + U)) = p (D • δ t) := by
    calc
      p (δ (t + U)) = p (B • δ t) := congrArg p (hδperiod t)
      _ = p (δ t) := LiZhongQC.s30a_p_smul hp hBΓ (δ t)
      _ = p (D • δ t) := (LiZhongQC.s30a_p_smul hp hDΓ (δ t)).symm
  have hwhole : (fun t : ℝ => δ (t + U)) = (fun t => D • δ t) :=
    hp.1.eq_of_comp_eq
      (hδ.1.continuous.comp (continuous_id.add continuous_const))
      ((continuous_const_smul D).comp hδ.1.continuous)
      (funext hproject) 0 hinit
  let η : ℝ → ℍ := fun t => C⁻¹ • δ t
  have hη : IsHGeodesicParam η := isHGeodesicParam_smul C⁻¹ hδ
  have hηperiod (t : ℝ) : η (t + U) = A • η t := by
    change C⁻¹ • δ (t + U) = A • (C⁻¹ • δ t)
    rw [congrFun hwhole t]
    dsimp only [D]
    simp only [mul_smul, inv_smul_smul]
  obtain ⟨hTU, hlen, c, hc⟩ := equivariant_hGeodesic_unique_up_to_shift
    A hA ht hγ hη hT hU hγperiod hηperiod
  refine ⟨hTU, hlen, c, ?_⟩
  intro t
  rw [hc t]
  exact LiZhongQC.s30a_p_smul hp (Γ.inv_mem hC) (δ (t + c))

end LowDimensionalTopology.Geometry.Hyperbolic
