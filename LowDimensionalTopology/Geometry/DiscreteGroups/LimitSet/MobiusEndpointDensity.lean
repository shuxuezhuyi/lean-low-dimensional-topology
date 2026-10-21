/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.LimitSets
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscTrapping
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section
local instance endpointDensityQuaternionAction :
    MulAction Mobius.complexMobiusGroup (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :=
      nonElementaryQuaternionMulAction

/-- Genuine loxodromicity is unchanged by inversion of the actual full-space action. -/
theorem mobiusLoxodromic_inv {f : Mobius.complexMobiusGroup} (hf : Mobius.MobiusLoxodromic f) :
    Mobius.MobiusLoxodromic f⁻¹ := by
  have he : Mobius.mobiusExtendedFixedPoints f⁻¹ = Mobius.mobiusExtendedFixedPoints f := by
    ext q
    change f⁻¹ • q = q ↔ f • q = q
    rw [inv_smul_eq_iff, eq_comm]
  exact ⟨inv_ne_one.mpr hf.1, he ▸ hf.2⟩

/-- Inversion exchanges the actual attracting and repelling labels. -/
theorem IsMobiusAttractingRepellingPair.inverse {f : Mobius.complexMobiusGroup}
    {a b : Mobius.ExtendedComplex} (h : Mobius.IsMobiusAttractingRepellingPair f a b) :
    Mobius.IsMobiusAttractingRepellingPair f⁻¹ b a := by
  refine ⟨h.1.symm, Mobius.mobius_inv_fixed h.2.2.1, Mobius.mobius_inv_fixed h.2.1,
    h.2.2.2.2, ?_⟩
  simpa only [inv_inv] using h.2.2.2.1

/-- Each open limit-set neighborhood contains the attracting endpoint of a genuine loxodromic element. -/
theorem mobius_exists_loxodromic_attracting_in_open (H : Subgroup Mobius.complexMobiusGroup)
    (U : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hUL : (U ∩ mobiusLimitSet H).Nonempty) :
    ∃ g : H, Mobius.MobiusLoxodromic g.val ∧ ∃ a b : Mobius.ExtendedComplex,
      Mobius.IsMobiusAttractingRepellingPair g.val a b ∧ a ∈ U := by
  obtain ⟨z, hzU, hzL⟩ := hUL
  obtain ⟨w, hwU, g, hg, hfix⟩ := mem_closure_iff.mp hzL U hU hzU
  obtain ⟨a, b, hp⟩ := Mobius.mobius_loxodromic_attracting_repelling g.val hg
  rcases (mobius_attracting_repelling_fixed_iff g.val hg.1 a b hp w).mp hfix with hwa | hwb
  · exact ⟨g, hg, a, b, hp, hwa ▸ hwU⟩
  · exact ⟨g⁻¹, mobiusLoxodromic_inv hg, b, a,
      DiscreteGroups.IsMobiusAttractingRepellingPair.inverse hp, hwb ▸ hwU⟩

/-- Infinite actual point orbits provide loxodromic attracting/repelling pairs outside every finite set. -/
theorem nonElementary_exists_loxodromic_endpoints_avoid_finite
    (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (S : Set Mobius.ExtendedComplex) (hS : S.Finite) :
    ∃ g : H, Mobius.MobiusLoxodromic g.val ∧ ∃ a b : Mobius.ExtendedComplex,
      Mobius.IsMobiusAttractingRepellingPair g.val a b ∧ a ∉ S ∧ b ∉ S := by
  obtain ⟨f, hfH, hfL⟩ := nonElementary_exists_loxodromic H hH
  obtain ⟨a, b, hp⟩ := Mobius.mobius_loxodromic_attracting_repelling f hfL
  have hF : ({a, b} : Set Mobius.ExtendedComplex).Finite := (Set.finite_singleton b).insert a
  obtain ⟨u, hu⟩ := exists_disjoint_translate_of_finite_sets
    (nonElementary_boundary_orbit_infinite H hH) hF hS
  let g : H := u * ⟨f, hfH⟩ * u⁻¹
  refine ⟨g, Mobius.mobiusLoxodromic_conjugation_forward f u.val hfL,
    u • a, u • b, hp.conjugation u.val, ?_, ?_⟩
  · intro ha
    exact Set.disjoint_left.mp hu ⟨a, Or.inl rfl, rfl⟩ ha
  · intro hb
    exact Set.disjoint_left.mp hu ⟨b, Or.inr rfl, rfl⟩ hb

/-- The compact-uniform dynamical conclusion uses the already chosen attracting/repelling labels. -/
theorem IsMobiusAttractingRepellingPair.uniformlyOn {f : Mobius.complexMobiusGroup}
    {a b : Mobius.ExtendedComplex} (h : Mobius.IsMobiusAttractingRepellingPair f a b)
    (hf : Mobius.MobiusLoxodromic f) (K : Set Mobius.ExtendedComplex) (hK : IsCompact K) (hb : b ∉ K) :
    Mobius.MobiusIteratesConvergeUniformlyOn f a K := by
  obtain ⟨c, d, hcd, hc, hd, hfor, hunif⟩ := Mobius.loxodromic_iterates_tendsto_attractor_uniformly_off_repeller f hf
  obtain ⟨z, _, hz⟩ := Set.infinite_univ.exists_notMem_finite
    ((Set.finite_singleton d).insert b)
  have hzb : z ≠ b := fun he => hz (Or.inl he)
  have hzd : z ≠ d := fun he => hz (Or.inr he)
  have hca : c = a := tendsto_nhds_unique (hfor z hzd) (h.2.2.2.1 z hzb)
  subst c
  rcases (mobius_attracting_repelling_fixed_iff f hf.1 a b h d).mp hd with hda | hdb
  · exact False.elim (hcd hda.symm)
  · subst d
    exact hunif K hK hb

/-- Genuine round discs form a neighborhood basis at every point of the actual sphere. -/
theorem mobius_roundDisc_closure_basis (z : Mobius.ExtendedComplex) (U : Set Mobius.ExtendedComplex)
    (hU : IsOpen U) (hz : z ∈ U) :
    ∃ D : Set Mobius.ExtendedComplex, Mobius.IsComplexOpenDisc D ∧ z ∈ D ∧ closure D ⊆ U := by
  obtain ⟨b, hb⟩ := exists_ne z
  obtain ⟨q, hq, _⟩ := mobius_exists_send_pair_zero_infty z b (Ne.symm hb)
  obtain ⟨r, hr, hD, hzD, hcl⟩ := mobiusNormalizedDisc_closure_basis q z hq U hU hz
  exact ⟨mobiusNormalizedDisc q r, hD, hzD, hcl⟩

/-- Both endpoints can be placed in one open limit-set neighborhood, with a prescribed point avoided. -/
theorem nonElementary_exists_loxodromic_pair_in_open
    (H : Subgroup Mobius.complexMobiusGroup) (hH : IsNonElementary H)
    (U : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hUL : (U ∩ mobiusLimitSet H).Nonempty)
    (c : Mobius.ExtendedComplex) :
    ∃ g : H, Mobius.MobiusLoxodromic g.val ∧ ∃ a b : Mobius.ExtendedComplex,
      Mobius.IsMobiusAttractingRepellingPair g.val a b ∧ a ∈ U ∧ b ∈ U ∧ a ≠ c := by
  obtain ⟨p, hpL, ap, bp, hp, hapU⟩ := mobius_exists_loxodromic_attracting_in_open H U hU hUL
  obtain ⟨f, hfL, a, b, hf, ha, hb⟩ :=
    nonElementary_exists_loxodromic_endpoints_avoid_finite H hH {ap, bp}
      ((Set.finite_singleton bp).insert ap)
  have haap : a ≠ ap := fun he => ha (Or.inl he)
  have habp : a ≠ bp := fun he => ha (Or.inr he)
  have hbbp : b ≠ bp := fun he => hb (Or.inr he)
  have haU := (hp.2.2.2.1 a habp).eventually (hU.mem_nhds hapU)
  have hbU := (hp.2.2.2.1 b hbbp).eventually (hU.mem_nhds hapU)
  have hne : ∀ᶠ m : ℕ in atTop, (p.val ^ m).val a ≠ c := by
    by_cases hac : ap = c
    · exact Eventually.of_forall fun m => hac ▸ Mobius.mobius_pow_ne_fixed hp.2.1 haap m
    · exact (hp.2.2.2.1 a habp).eventually (isClosed_singleton.isOpen_compl.mem_nhds hac)
  obtain ⟨m, hm⟩ := (haU.and (hbU.and hne)).exists
  let g : H := (p ^ m) * f * (p ^ m)⁻¹
  exact ⟨g, Mobius.mobiusLoxodromic_conjugation_forward f.val (p ^ m).val hfL,
    (p.val ^ m).val a, (p.val ^ m).val b,
    Mobius.IsMobiusAttractingRepellingPair.conjugation hf (p ^ m).val,
    hm.1, hm.2.1, hm.2.2⟩

/-- genuine loxodromic fixed points meet two prescribed limit neighborhoods. -/
theorem exists_loxodromic_fixedPoints_in_disjoint_limit_neighbourhoods (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsNonElementary H)
    (U V : Set Mobius.ExtendedComplex) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hUL : (U ∩ mobiusLimitSet H).Nonempty) (hVL : (V ∩ mobiusLimitSet H).Nonempty) :
    ∃ F : H, Mobius.MobiusLoxodromic F.val ∧ ∃ a ∈ U, ∃ b ∈ V,
      F.val.val a = a ∧ F.val.val b = b := by
  obtain ⟨q, hqL, aq, bq, hq, haqV⟩ := mobius_exists_loxodromic_attracting_in_open H V hV hVL
  obtain ⟨g, hgL, a, b, hg, haU, hbU, habq⟩ :=
    nonElementary_exists_loxodromic_pair_in_open H hH U hU hUL bq
  have hqevent := (hq.2.2.2.1 a habq).eventually (hV.mem_nhds haqV)
  obtain ⟨r, hr⟩ := hqevent.exists
  let h : H := q ^ r
  have hhaV : h.val.val a ∈ V := hr
  obtain ⟨E, hE, hbE, hclE⟩ := mobius_roundDisc_closure_basis b U hU hbU
  obtain ⟨K, hK, hhaK, hclK⟩ := mobius_roundDisc_closure_basis (h.val.val a) V hV hhaV
  have hbK : b ∉ closure K := fun hh => Set.disjoint_left.mp hUV hbU (hclK hh)
  have hUF := DiscreteGroups.IsMobiusAttractingRepellingPair.uniformlyOn hg hgL (closure K)
    isClosed_closure.isCompact hbK
  have hpre : h.val.val ⁻¹' K ∈ 𝓝 a :=
    (hK.isOpen.preimage (Mobius.continuous_mobiusBoundary h.val)).mem_nhds hhaK
  have hforward := (Mobius.mobiusIteratesConvergeUniformlyOn_iff g.val a (closure K)).mp hUF
    (h.val.val ⁻¹' K) hpre
  let L := (h⁻¹).val.val '' closure E
  have hLc : IsCompact L := isClosed_closure.isCompact.image (Mobius.continuous_mobiusBoundary (h⁻¹).val)
  have haL : a ∉ L := by
    rintro ⟨x, hx, hxa⟩
    have hax : h.val.val a = x := by
      rw [← hxa]
      exact h.val.val.apply_symm_apply x
    exact Set.disjoint_left.mp hUV (hclE (hax ▸ hx)) hhaV
  have hUB := DiscreteGroups.IsMobiusAttractingRepellingPair.uniformlyOn
    (DiscreteGroups.IsMobiusAttractingRepellingPair.inverse hg) (mobiusLoxodromic_inv hgL) L hLc haL
  have hbackward := (Mobius.mobiusIteratesConvergeUniformlyOn_iff g.val⁻¹ b L).mp hUB
    E (hE.isOpen.mem_nhds hbE)
  obtain ⟨n, hnf, hnb⟩ := (hforward.and hbackward).exists
  let F : H := h * g ^ n
  have hFK : F.val.val '' closure K ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    exact hnf x hx
  have hInvE : (F⁻¹).val.val '' closure E ⊆ E := by
    rintro y ⟨x, hx, rfl⟩
    change ((h.val * g.val ^ n)⁻¹).val x ∈ E
    rw [mul_inv_rev, ← inv_pow]
    exact hnb _ ⟨x, hx, rfl⟩
  obtain ⟨v, hvK, hFL, hFv⟩ := mobius_disc_trapping_fixed_point K F.val hK hFK
  obtain ⟨u, huE, _, hIu⟩ := mobius_disc_trapping_fixed_point E (F⁻¹).val hE hInvE
  have hFu : F.val.val u = u := by
    change (F.val⁻¹).val u = u at hIu
    simpa only [inv_inv] using (Mobius.mobius_inv_fixed (f := F.val⁻¹) hIu)
  exact ⟨F, hFL, u, hclE (subset_closure huE), v, hclK (subset_closure hvK), hFu, hFv⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
