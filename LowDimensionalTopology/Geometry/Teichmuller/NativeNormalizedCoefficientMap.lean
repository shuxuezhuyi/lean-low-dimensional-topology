module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation
public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding

/-!
# The actual normalized quasiconformal map on coefficient measure classes

The base coefficient is an element of the original compatible L-infinity ball.
Its normalized symmetric solution and inverse preserve the actual upper half
plane. Their null-set preservation gives quasi-measure-preserving maps for the
existing hyperbolic area; no preservation of that area is asserted.

The normalized-solution identities and quasiconformal null-set results use
Wu Xiaobin's LiZhongQC development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

/-- Restrict an actual map preserving the upper half plane to its original carrier. -/
def upperRestriction (f : ℂ → ℂ)
    (hf : MapsTo f LiZhongQC.upperHalf LiZhongQC.upperHalf) : ℍ → ℍ :=
  fun z => ⟨f z, hf z.im_pos⟩

@[simp] theorem upperRestriction_coe (f : ℂ → ℂ)
    (hf : MapsTo f LiZhongQC.upperHalf LiZhongQC.upperHalf) (z : ℍ) :
    (upperRestriction f hf z : ℂ) = f z := rfl

/-- Planar null-set preservation passes to the unchanged hyperbolic measure class. -/
theorem upperRestriction_quasiMeasurePreserving (f : ℂ → ℂ)
    (hf : QuasiMeasurePreserving f (volume : Measure ℂ) volume)
    (hU : MapsTo f LiZhongQC.upperHalf LiZhongQC.upperHalf) :
    QuasiMeasurePreserving (upperRestriction f hU)
      (volume : Measure ℍ) volume := by
  have hm : Measurable (upperRestriction f hU) := by
    apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
    exact hf.measurable.comp UpperHalfPlane.measurable_coe
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hm hs]
  apply measure_eq_zero_iff_ae_notMem.mpr
  let P : ℂ → Prop := fun z => ∀ hz : 0 < z.im, (⟨z, hz⟩ : ℍ) ∉ s
  have hn : ∀ᵐ z : ℍ ∂volume, P (z : ℂ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs0] with z hz
    exact fun _ => hz
  have hr := ae_plane_iff.mpr hn
  have hp : ∀ᵐ z : ℂ ∂volume, P z := by
    have hh := (ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet).mp hr
    filter_upwards [hh] with z hz
    exact fun hzU => hz hzU hzU
  have hout := ae_plane_iff.mp (ae_restrict_of_ae (hf.ae hp))
  filter_upwards [hout] with z hz
  exact hz (hU z.im_pos)

variable {Γ : Subgroup Deck}

/-- The actual normalized symmetric solution of the base coefficient. -/
def normalizedMap (ν : Ball Γ) : ℂ → ℂ :=
  LiZhongQC.fMuSym (planeRepresentative ν.val.val)

/-- The actual inverse of that same normalized plane map. -/
def normalizedInverse (ν : Ball Γ) : ℂ → ℂ :=
  Function.invFunOn (normalizedMap ν) Set.univ

theorem normalizedMap_spec (ν : Ball Γ) :
    ∃ K : ℝ, LiZhongQC.IsKQC (normalizedMap ν) univ K ∧
      normalizedMap ν '' univ = univ ∧ normalizedMap ν 0 = 0 ∧ normalizedMap ν 1 = 1 ∧
      (∀ z, normalizedMap ν (conj z) = conj (normalizedMap ν z)) ∧
      normalizedMap ν '' LiZhongQC.upperHalf = LiZhongQC.upperHalf ∧
      ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
        LiZhongQC.complexDilatation (normalizedMap ν) z = planeRepresentative ν.val.val z :=
  LiZhongQC.b33_t_fs_spec (toSourceGamma ν).val

theorem normalizedInverse_spec (ν : Ball Γ) :
    ∃ K : ℝ, LiZhongQC.IsKQC (normalizedInverse ν) univ K ∧
      (∀ z, normalizedInverse ν (normalizedMap ν z) = z) ∧
      (∀ z, normalizedMap ν (normalizedInverse ν z) = z) ∧
      ∀ z, normalizedInverse ν (conj z) = conj (normalizedInverse ν z) :=
  LiZhongQC.b33_t_fs_inv_spec (toSourceGamma ν).val

theorem normalizedMap_mapsTo_upper (ν : Ball Γ) :
    MapsTo (normalizedMap ν) LiZhongQC.upperHalf LiZhongQC.upperHalf := by
  obtain ⟨_, _, _, _, _, _, hU, _⟩ := normalizedMap_spec ν
  intro z hz
  rw [← hU]
  exact mem_image_of_mem _ hz

theorem normalizedInverse_mapsTo_upper (ν : Ball Γ) :
    MapsTo (normalizedInverse ν) LiZhongQC.upperHalf LiZhongQC.upperHalf := by
  obtain ⟨_, _, _, _, _, _, hU, _⟩ := normalizedMap_spec ν
  obtain ⟨_, _, hleft, _, _⟩ := normalizedInverse_spec ν
  intro z hz
  obtain ⟨w, hw, he⟩ := hU.symm ▸ hz
  rw [← he, hleft]
  exact hw

/-- The actual normalized map, restricted to the original upper half plane. -/
def normalizedUpperEquiv (ν : Ball Γ) : ℍ ≃ ℍ where
  toFun := upperRestriction (normalizedMap ν) (normalizedMap_mapsTo_upper ν)
  invFun := upperRestriction (normalizedInverse ν) (normalizedInverse_mapsTo_upper ν)
  left_inv z := by
    apply UpperHalfPlane.ext
    exact (normalizedInverse_spec ν).choose_spec.2.1 (z : ℂ)
  right_inv z := by
    apply UpperHalfPlane.ext
    exact (normalizedInverse_spec ν).choose_spec.2.2.1 (z : ℂ)

@[simp] theorem normalizedUpperEquiv_coe (ν : Ball Γ) (z : ℍ) :
    (normalizedUpperEquiv ν z : ℂ) = normalizedMap ν z := rfl

@[simp] theorem normalizedUpperEquiv_symm_coe (ν : Ball Γ) (z : ℍ) :
    ((normalizedUpperEquiv ν).symm z : ℂ) = normalizedInverse ν z := rfl

theorem normalizedInverse_quasiMeasurePreserving (ν : Ball Γ) :
    QuasiMeasurePreserving (normalizedInverse ν) (volume : Measure ℂ) volume := by
  obtain ⟨K, hK, hs, _, _, _, _, _⟩ := normalizedMap_spec ν
  exact LiZhongQC.ahT_qmp_inv ⟨K, hK⟩ hs

theorem normalizedMap_quasiMeasurePreserving (ν : Ball Γ) :
    QuasiMeasurePreserving (normalizedMap ν) (volume : Measure ℂ) volume := by
  obtain ⟨_, hK, _, _, _, _, _, _⟩ := normalizedMap_spec ν
  obtain ⟨_, hI, hleft, _, _⟩ := normalizedInverse_spec ν
  have hm : Measurable (normalizedMap ν) :=
    (continuousOn_univ.mp hK.2.2.1.1).measurable
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hm hs]
  have hsub : normalizedMap ν ⁻¹' s ⊆ normalizedInverse ν '' s := by
    intro z hz
    exact ⟨normalizedMap ν z, hz, hleft z⟩
  exact measure_mono_null hsub (LiZhongQC.thm9_6_cor1_null hI (subset_univ s) hs0)

theorem normalizedUpperEquiv_quasiMeasurePreserving (ν : Ball Γ) :
    QuasiMeasurePreserving (normalizedUpperEquiv ν) (volume : Measure ℍ) volume :=
  upperRestriction_quasiMeasurePreserving (normalizedMap ν)
    (normalizedMap_quasiMeasurePreserving ν) (normalizedMap_mapsTo_upper ν)

theorem normalizedUpperEquiv_symm_quasiMeasurePreserving (ν : Ball Γ) :
    QuasiMeasurePreserving (normalizedUpperEquiv ν).symm (volume : Measure ℍ) volume :=
  upperRestriction_quasiMeasurePreserving (normalizedInverse ν)
    (normalizedInverse_quasiMeasurePreserving ν) (normalizedInverse_mapsTo_upper ν)

/-- The original coefficient is the actual complex dilatation on the upper half plane. -/
theorem normalizedMap_dilatation_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, LiZhongQC.complexDilatation (normalizedMap ν) z = ν.val.val z := by
  obtain ⟨_, _, _, _, _, _, _, hd⟩ := normalizedMap_spec ν
  simpa only [planeRepresentative_coe] using ae_plane_iff.mp hd

/-- The literal unit phase of the actual normalized derivative. -/
def derivativePhase (ν : Ball Γ) (z : ℍ) : ℂ :=
  LiZhongQC.dz (normalizedMap ν) z / conj (LiZhongQC.dz (normalizedMap ν) z)

theorem derivativePhase_aestronglyMeasurable (ν : Ball Γ) :
    AEStronglyMeasurable (derivativePhase ν) (volume : Measure ℍ) := by
  have hm : AEStronglyMeasurable
      (fun z : ℍ => LiZhongQC.dz (normalizedMap ν) z) volume :=
    ((LiZhongQC.measurable_dz (normalizedMap ν)).comp
      UpperHalfPlane.measurable_coe).aestronglyMeasurable
  exact hm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hm)

theorem norm_derivativePhase_le (ν : Ball Γ) (z : ℍ) :
    ‖derivativePhase ν z‖ ≤ 1 :=
  LiZhongQC.ahT_norm_div_conj_le _

/-- Positive Jacobian supplies the actual phase's unit norm almost everywhere. -/
theorem norm_derivativePhase_ae (ν : Ball Γ) :
    ∀ᵐ z : ℍ ∂volume, ‖derivativePhase ν z‖ = 1 := by
  obtain ⟨_, hK, _, _, _, _, _, _⟩ := normalizedMap_spec ν
  have hJ := LiZhongQC.thm9_6_cor2_jacobian_pos hK
  rw [Measure.restrict_univ] at hJ
  filter_upwards [ae_plane_iff.mp (ae_restrict_of_ae hJ)] with z hz
  have hd : LiZhongQC.dz (normalizedMap ν) z ≠ 0 := by
    intro he
    unfold LiZhongQC.jacobian at hz
    rw [he, norm_zero] at hz
    nlinarith [sq_nonneg ‖LiZhongQC.dzbar (normalizedMap ν) z‖]
  rw [derivativePhase, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hd)]

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
