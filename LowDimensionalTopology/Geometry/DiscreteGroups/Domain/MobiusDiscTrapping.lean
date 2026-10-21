/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperbolicExamples
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.Order.Compact
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The norm of the complex identity function has no local maximum. -/
theorem discTrap_complex_norm_not_localMax (z : ℂ) : ¬IsLocalMax (fun w : ℂ => ‖w‖) z := by
  intro h
  have hc : ∀ᶠ w : ℂ in 𝓝 z, w = z :=
    Complex.eventually_eq_of_isLocalMax_norm (f := fun w : ℂ => w)
      (Eventually.of_forall fun _ => differentiableAt_id) h
  have hs : IsOpen ({z} : Set ℂ) := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have hwz : w = z := Set.mem_singleton_iff.mp hw
    subst w
    exact hc
  exact not_isOpen_singleton z hs

/-- A norm-preserving map cannot send a nonempty compact set into its own open interior. -/
theorem discTrap_no_norm_preserving_compact_trap {K U : Set ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hU : IsOpen U) (hUK : U ⊆ K)
    (f : ℂ → ℂ) (hfnorm : ∀ z, ‖f z‖ = ‖z‖) (htrap : f '' K ⊆ U) : False := by
  obtain ⟨z, hz, hzmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hw : f z ∈ U := htrap ⟨z, hz, rfl⟩
  apply discTrap_complex_norm_not_localMax (f z)
  filter_upwards [hU.mem_nhds hw] with w hw
  rw [hfnorm]
  exact hzmax (hUK hw)

/-- A compact sphere set avoiding infinity has compact finite coordinates. -/
theorem discTrap_isCompact_finite_part {K : Set Mobius.ExtendedComplex}
    (hK : IsCompact K) (hinf : ∞ ∉ K) :
    IsCompact (((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' K) := by
  apply OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage' hK
  intro z hz
  obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hinf (he ▸ hz))
  exact ⟨w, rfl⟩

/-- Nonempty sets avoiding infinity have nonempty finite coordinates. -/
theorem discTrap_nonempty_finite_part {K : Set Mobius.ExtendedComplex}
    (hne : K.Nonempty) (hinf : ∞ ∉ K) :
    (((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' K).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hinf (he ▸ hz))
  exact ⟨w, hz⟩

/-- A strict trap gives a reverse strict trap on the complementary side. -/
theorem discTrap_inverse_compl (f : Equiv.Perm Mobius.ExtendedComplex) {K D : Set Mobius.ExtendedComplex}
    (htrap : f '' K ⊆ D) : f.symm '' Dᶜ ⊆ Kᶜ := by
  rintro _ ⟨x, hx, rfl⟩ hy
  exact hx (htrap ⟨f.symm x, hy, f.apply_symm_apply x⟩)

/-- A nontranslation unit-modulus standard map has no strict open-set trap. -/
theorem discTrap_standard_unit_no_trap (k : ℂˣ) (hk : (k : ℂ) ≠ 1) (hkn : ‖(k : ℂ)‖ = 1)
    {D : Set Mobius.ExtendedComplex} (hD : IsOpen D) (hne : D.Nonempty) (hcne : Dᶜ.Nonempty)
    (htrap : (Mobius.mobiusStandardElement k : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) : False := by
  by_cases hinf : ∞ ∈ closure D
  · have hiD : ∞ ∈ D := htrap ⟨∞, hinf, Mobius.mobiusStandardElement_infty k⟩
    have hiL : ∞ ∉ Dᶜ := fun h => h hiD
    have hK := discTrap_isCompact_finite_part hD.isClosed_compl.isCompact hiL
    have hKne := discTrap_nonempty_finite_part hcne hiL
    have hU : IsOpen (((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' (closure D)ᶜ) :=
      isClosed_closure.isOpen_compl.preimage OnePoint.continuous_coe
    have hUK : ((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' (closure D)ᶜ ⊆
        ((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' Dᶜ := fun z hz hzd => hz (subset_closure hzd)
    have hki : ((k⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      simpa only [Units.val_inv_eq_inv_val, inv_ne_one] using hk
    have hkin : ‖((k⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hkn, inv_one]
    apply discTrap_no_norm_preserving_compact_trap hK hKne hU hUK
      (fun z => ((k⁻¹ : ℂˣ) : ℂ) * z) (fun z => by rw [norm_mul, hkin, one_mul])
    rintro _ ⟨z, hz, rfl⟩
    have hm := discTrap_inverse_compl (Mobius.mobiusStandardElement k : Equiv.Perm Mobius.ExtendedComplex) htrap
    have hz' := hm ⟨(z : Mobius.ExtendedComplex), hz, rfl⟩
    change (((Mobius.mobiusStandardElement k)⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex)
      (z : Mobius.ExtendedComplex) ∈ (closure D)ᶜ at hz'
    rw [Mobius.mobiusStandardElement_inv k hk, Mobius.mobiusStandardElement_coe] at hz'
    change ((((k⁻¹ : ℂˣ) : ℂ) * z : ℂ) : Mobius.ExtendedComplex) ∈ (closure D)ᶜ
    simpa only [ite_eq_right hki, add_zero] using hz'
  · have hK := discTrap_isCompact_finite_part (isClosed_closure.isCompact : IsCompact (closure D)) hinf
    have hKne := discTrap_nonempty_finite_part (hne.mono subset_closure) hinf
    have hU : IsOpen (((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' D) :=
      hD.preimage OnePoint.continuous_coe
    have hUK : ((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' D ⊆
        ((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' closure D := fun z hz => subset_closure hz
    apply discTrap_no_norm_preserving_compact_trap hK hKne hU hUK
      (fun z => (k : ℂ) * z) (fun z => by rw [norm_mul, hkn, one_mul])
    rintro _ ⟨z, hz, rfl⟩
    have hz' := htrap ⟨(z : Mobius.ExtendedComplex), hz, rfl⟩
    rw [Mobius.mobiusStandardElement_coe] at hz'
    change (((k : ℂ) * z : ℂ) : Mobius.ExtendedComplex) ∈ D
    simpa only [ite_eq_right hk, add_zero] using hz'

/-- Strict trapping is transported by actual Mobius conjugacy. -/
theorem discTrap_conjugation (f q : Mobius.complexMobiusGroup) {D : Set Mobius.ExtendedComplex}
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) :
    ((q * f * q⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) ''
      closure ((q : Equiv.Perm Mobius.ExtendedComplex) '' D) ⊆ (q : Equiv.Perm Mobius.ExtendedComplex) '' D := by
  have hcl : closure ((q : Equiv.Perm Mobius.ExtendedComplex) '' D) =
      (q : Equiv.Perm Mobius.ExtendedComplex) '' closure D :=
    ((Mobius.mobiusBoundaryHomeomorph q).image_closure D).symm
  rintro _ ⟨z, hz, rfl⟩
  rw [hcl] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨(f : Equiv.Perm Mobius.ExtendedComplex) w, htrap ⟨w, hw, rfl⟩, ?_⟩
  change (q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex) w) =
    (q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex)
      ((q : Equiv.Perm Mobius.ExtendedComplex).symm ((q : Equiv.Perm Mobius.ExtendedComplex) w)))
  rw [Equiv.symm_apply_apply]

/-- A genuine elliptic transformation cannot strictly trap an open nonempty proper sphere subset. -/
theorem discTrap_elliptic_no_trap (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusElliptic f)
    {D : Set Mobius.ExtendedComplex} (hD : IsOpen D) (hne : D.Nonempty) (hcne : Dᶜ.Nonempty)
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) : False := by
  obtain ⟨k, hk, hkn, hc⟩ := (Mobius.mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hc
  have ht := discTrap_conjugation f q htrap
  rw [hq] at ht
  have hopen : IsOpen ((q : Equiv.Perm Mobius.ExtendedComplex) '' D) :=
    (Mobius.mobiusBoundaryHomeomorph q).isOpenMap D hD
  have hcne' : ((q : Equiv.Perm Mobius.ExtendedComplex) '' D)ᶜ.Nonempty := by
    obtain ⟨z, hz⟩ := hcne
    refine ⟨(q : Equiv.Perm Mobius.ExtendedComplex) z, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact hz ((q : Equiv.Perm Mobius.ExtendedComplex).injective hwz ▸ hw)
  exact discTrap_standard_unit_no_trap k hk hkn hopen (hne.image q.val) hcne' ht

/-- Forward iterates stay inside a forward-invariant sphere set. -/
theorem discTrap_iterates_mem (f : Mobius.complexMobiusGroup) {A : Set Mobius.ExtendedComplex}
    (hA : ∀ z ∈ A, (f : Equiv.Perm Mobius.ExtendedComplex) z ∈ A)
    (z : Mobius.ExtendedComplex) (hz : z ∈ A) (n : ℕ) :
    ((f ^ n : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) z ∈ A := by
  induction n with
  | zero => exact hz
  | succ n hn =>
      rw [pow_succ']
      change (f : Equiv.Perm Mobius.ExtendedComplex)
        (((f ^ n : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) z) ∈ A
      exact hA _ hn

/-- A convergent orbit starting in the compact trapped image has its limit in that image. -/
theorem discTrap_limit_mem_image (f : Mobius.complexMobiusGroup) {K D : Set Mobius.ExtendedComplex}
    (hK : IsCompact K) (hDK : D ⊆ K)
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' K ⊆ D)
    {z a : Mobius.ExtendedComplex} (hz : z ∈ (f : Equiv.Perm Mobius.ExtendedComplex) '' K)
    (hlim : Tendsto (fun n : ℕ => ((f ^ n : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) z)
      atTop (𝓝 a)) : a ∈ (f : Equiv.Perm Mobius.ExtendedComplex) '' K := by
  have hmap : ∀ w ∈ (f : Equiv.Perm Mobius.ExtendedComplex) '' K,
      (f : Equiv.Perm Mobius.ExtendedComplex) w ∈ (f : Equiv.Perm Mobius.ExtendedComplex) '' K :=
    fun w hw => ⟨w, hDK (htrap hw), rfl⟩
  exact (hK.image (Mobius.continuous_mobiusBoundary f)).isClosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n => discTrap_iterates_mem f hmap z hz n)

/-- Inversion preserves the unique-boundary-fixed-point definition of parabolic. -/
theorem discTrap_parabolic_inv (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f) :
    Mobius.MobiusParabolic f⁻¹ := by
  obtain ⟨p, hp⟩ := hf.2
  refine ⟨inv_ne_one.mpr hf.1, p, fun z => ?_⟩
  apply Iff.trans ?_ (hp z)
  change f⁻¹ • z = z ↔ f • z = z
  rw [inv_smul_eq_iff]
  exact eq_comm

/-- A parabolic map cannot strictly trap an open nonempty proper sphere subset. -/
theorem discTrap_parabolic_no_trap (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f)
    {D : Set Mobius.ExtendedComplex} (hD : IsOpen D) (hne : D.Nonempty) (hcne : Dᶜ.Nonempty)
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) : False := by
  obtain ⟨a, ha, hlim⟩ := Mobius.mobius_parabolic_iterates_tendsto f hf
  obtain ⟨b, hb, hlimInv⟩ := Mobius.mobius_parabolic_iterates_tendsto f⁻¹ (discTrap_parabolic_inv f hf)
  obtain ⟨p, hp⟩ := hf.2
  have hbf : (f : Equiv.Perm Mobius.ExtendedComplex) b = b := by
    have he := congrArg (f : Equiv.Perm Mobius.ExtendedComplex) hb
    change (f : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex).symm b) =
      (f : Equiv.Perm Mobius.ExtendedComplex) b at he
    simpa only [Equiv.apply_symm_apply] using he.symm
  have hba : b = a := ((hp b).mp hbf).trans ((hp a).mp ha).symm
  obtain ⟨z, hz⟩ := hne
  have hzimage : (f : Equiv.Perm Mobius.ExtendedComplex) z ∈
      (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D := ⟨z, subset_closure hz, rfl⟩
  have haimage := discTrap_limit_mem_image f (isClosed_closure.isCompact : IsCompact (closure D))
    subset_closure htrap hzimage (hlim ((f : Equiv.Perm Mobius.ExtendedComplex) z))
  have haD : a ∈ D := htrap haimage
  obtain ⟨w, hw⟩ := hcne
  have hback : ∀ x ∈ Dᶜ, ((f⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) x ∈ Dᶜ := by
    intro x hx hix
    apply hx
    exact htrap ⟨((f⁻¹ : Mobius.complexMobiusGroup) : Equiv.Perm Mobius.ExtendedComplex) x,
      subset_closure hix, (f : Equiv.Perm Mobius.ExtendedComplex).apply_symm_apply x⟩
  have hbout : b ∈ Dᶜ := hD.isClosed_compl.mem_of_tendsto (hlimInv w)
    (Eventually.of_forall fun n => discTrap_iterates_mem f⁻¹ hback w hw n)
  exact hbout (hba ▸ haD)

/-- A genuine generalized open disc is not closed in the sphere. -/
theorem discTrap_openDisc_not_isClosed {D : Set Mobius.ExtendedComplex} (hD : Mobius.IsComplexOpenDisc D) :
    ¬IsClosed D := by
  obtain ⟨q, hq⟩ := hD.normalize
  intro hclosed
  have hc : IsClosed Hyperbolic.extendedUnitDisc := by
    rw [← hq]
    exact (Mobius.mobiusBoundaryHomeomorph q).isClosedMap D hclosed
  have hmem := Hyperbolic.unitCircle_mem_closure_extendedUnitDisc
    (ζ := (1 : ℂ)) (by norm_num)
  have hunit : ((1 : ℂ) : Mobius.ExtendedComplex) ∈ Hyperbolic.extendedUnitDisc := hc.closure_subset hmem
  have hnorm := (Hyperbolic.coe_mem_extendedUnitDisc (1 : ℂ)).mp hunit
  norm_num at hnorm

/--
A strict generalized-disc trap is genuinely loxodromic,
with a fixed point in the actual image of the closed disc.
-/
theorem loxodromic_and_fixedPoint_of_disc_closure_strictly_trapped (f : Mobius.complexMobiusGroup) {D : Set
    Mobius.ExtendedComplex}
    (hD : Mobius.IsComplexOpenDisc D)
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) :
    Mobius.MobiusLoxodromic f ∧ ∃ v ∈ (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D,
      (f : Equiv.Perm Mobius.ExtendedComplex) v = v := by
  have hnotClosed := discTrap_openDisc_not_isClosed hD
  have hInf : D.Infinite := fun hfinite => hnotClosed hfinite.isClosed
  have hne := hInf.nonempty
  have hcne : Dᶜ.Nonempty := by
    by_contra h
    have huniv : D = Set.univ := by
      ext z
      simp only [mem_univ, iff_true]
      by_contra hz
      exact h ⟨z, hz⟩
    exact hnotClosed (by rw [huniv]; exact isClosed_univ)
  have hf : f ≠ 1 := by
    intro he
    subst f
    apply hnotClosed
    apply isClosed_of_closure_subset
    intro z hz
    exact htrap ⟨z, hz, rfl⟩
  have hL : Mobius.MobiusLoxodromic f := by
    rcases Mobius.mobius_nonidentity_type_trichotomy f hf with hp | hl | he
    · exact False.elim (discTrap_parabolic_no_trap f hp hD.isOpen hne hcne htrap)
    · exact hl
    · exact False.elim (discTrap_elliptic_no_trap f he hD.isOpen hne hcne htrap)
  obtain ⟨a, b, _, ha, hb, hlim, _⟩ := Mobius.loxodromic_iterates_tendsto_attractor_uniformly_off_repeller f hL
  obtain ⟨z, hz, hzb⟩ := hInf.exists_notMem_finite (Set.finite_singleton b)
  have hzb' : z ≠ b := by simpa only [mem_singleton_iff] using hzb
  have hfb : (f : Equiv.Perm Mobius.ExtendedComplex) z ≠ b := by
    intro he
    exact hzb' ((f : Equiv.Perm Mobius.ExtendedComplex).injective (he.trans hb.symm))
  have hzimage : (f : Equiv.Perm Mobius.ExtendedComplex) z ∈
      (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D := ⟨z, subset_closure hz, rfl⟩
  have haimage := discTrap_limit_mem_image f (isClosed_closure.isCompact : IsCompact (closure D))
    subset_closure htrap hzimage (hlim ((f : Equiv.Perm Mobius.ExtendedComplex) z) hfb)
  exact ⟨hL, a, haimage, ha⟩

/-- The open-disc fixed-point formulation used in subsequent limit-set arguments. -/
theorem mobius_disc_trapping_fixed_point (D : Set Mobius.ExtendedComplex) (f : Mobius.complexMobiusGroup)
    (hD : Mobius.IsComplexOpenDisc D)
    (htrap : (f : Equiv.Perm Mobius.ExtendedComplex) '' closure D ⊆ D) :
    ∃ v ∈ D, Mobius.MobiusLoxodromic f ∧ (f : Equiv.Perm Mobius.ExtendedComplex) v = v := by
  obtain ⟨hL, v, hv, hfix⟩ := loxodromic_and_fixedPoint_of_disc_closure_strictly_trapped f hD htrap
  exact ⟨v, htrap hv, hL, hfix⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
