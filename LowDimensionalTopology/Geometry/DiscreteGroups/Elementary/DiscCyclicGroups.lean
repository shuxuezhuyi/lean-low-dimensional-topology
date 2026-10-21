/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenAxes
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.LimitSets
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual translations along one real line form a cyclic group whenever their Mobius subgroup is discrete. -/
theorem discrete_real_translations_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H)
    (hT : ∀ f ∈ H, ∃ r : ℝ, f = mobiusTranslation (r : ℂ)) : IsCyclic H := by
  let L := translationDisplacements H
  let : DiscreteTopology L := translationDisplacements_discrete H hd
  let R : AddSubgroup ℝ :=
    { carrier := {r | (r : ℂ) ∈ L}
      zero_mem' := L.zero_mem
      add_mem' := by
        intro a b ha hb
        change ((a + b : ℝ) : ℂ) ∈ L
        rw [Complex.ofReal_add]
        exact L.add_mem ha hb
      neg_mem' := by
        intro a ha
        change ((-a : ℝ) : ℂ) ∈ L
        rw [Complex.ofReal_neg]
        exact L.neg_mem ha }
  let F : R →+ L :=
    { toFun := fun r => ⟨(r.val : ℂ), r.property⟩
      map_zero' := rfl
      map_add' := fun a b => Subtype.ext (Complex.ofReal_add a.val b.val) }
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext (Complex.ofReal_injective (congrArg (fun z : L => z.val) hab))
  have hFc : Continuous F := Continuous.subtype_mk
    (Complex.continuous_ofReal.comp continuous_subtype_val) _
  let : DiscreteTopology R := DiscreteTopology.of_continuous_injective hFc hFi
  let : IsAddCyclic R := AddSubgroup.isAddCyclic_iff_discreteTopology.mpr inferInstance
  have hFs : Function.Surjective F := by
    intro z
    obtain ⟨r, hr⟩ := hT _ z.property
    have hz : z.val = (r : ℂ) := mobiusTranslation_injective hr
    exact ⟨⟨r, by change (r : ℂ) ∈ L; rw [← hz]; exact z.property⟩, Subtype.ext hz.symm⟩
  let e : R ≃+ L := AddEquiv.ofBijective F ⟨hFi, hFs⟩
  let : IsAddCyclic L := e.isAddCyclic.mp inferInstance
  let eH := translationDisplacementEquiv H (fun f hf => by
    obtain ⟨r, hr⟩ := hT f hf
    exact ⟨(r : ℂ), hr⟩)
  exact eH.isCyclic.mp inferInstance

/-- Without nonidentity elliptics, the logarithmic modulus embeds a discrete endpoint-fixing group in a cyclic real subgroup. -/
theorem discrete_dilation_no_elliptics_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f) : IsCyclic H := by
  let φ := dilationLogModulusHom H hi
  have hφ : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro f hf
    have hker : f ∈ dilationRotationKernel H hi := hf
    rcases (dilationRotationKernel_mem_iff_one_or_elliptic H hi hz f).mp hker with he | he
    · change f = 1
      exact Subtype.ext he
    · exact False.elim (hno f.val f.property he)
  let : IsAddCyclic (dilationLogModulusRange H hi) := dilationLogModulusRange_isAddCyclic H hd hi hz
  let F : Additive H →+ dilationLogModulusRange H hi := φ.toAdditiveLeft.rangeRestrict
  have hFi : Function.Injective F := by
    intro a b hab
    exact hφ (congrArg (fun z : dilationLogModulusRange H hi => z.val) hab)
  let : IsAddCyclic (Additive H) := isAddCyclic_of_injective F hFi
  exact isAddCyclic_additive_iff.mp inferInstance

/-- With a common boundary fixed point, a loxodromic element forces the other endpoint to be fixed as well. -/
theorem discrete_loxodromic_common_fixed_cyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (w : Mobius.ExtendedComplex)
    (hfix : ∀ f ∈ H, f.val w = w) (g : Mobius.complexMobiusGroup) (hgH : g ∈ H)
    (hg : Mobius.MobiusLoxodromic g) (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f) : IsCyclic H := by
  obtain ⟨a, b, hab, hgfix⟩ := mobius_loxodromic_boundary_fixed_pair g hg
  have hw := (hgfix w).mp (hfix g hgH)
  obtain ⟨v, hwv, hgw, hgv⟩ : ∃ v, w ≠ v ∧ g.val w = w ∧ g.val v = v := by
    rcases hw with ha | hb
    · exact ⟨b, by simpa only [ha] using hab, hfix g hgH, (hgfix b).mpr (Or.inr rfl)⟩
    · exact ⟨a, by simpa only [hb] using hab.symm, hfix g hgH, (hgfix a).mpr (Or.inl rfl)⟩
  have hfixv : ∀ f ∈ H, f.val v = v := fun f hf =>
    discreteMobius_shared_loxodromic_endpoints H hd f g hf hgH hg w v hwv hgw hgv (hfix f hf)
  obtain ⟨q, hqw, hqv⟩ := mobius_exists_send_pair_zero_infty w v hwv
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let : DiscreteTopology H := hd
  have hKd : Mobius.IsDiscreteMobiusSubgroup K := DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hKi : K ≤ Mobius.mobiusInftyStabilizer :=
    mobius_subgroupConjugate_le_inftyStabilizer H v (fun f => hfixv f.val f.property) q hqv
  have hKz : ∀ f ∈ K, f.val (0 : ℂ) = (0 : ℂ) := by
    rintro f ⟨h, hh, rfl⟩
    rw [← hqw]
    exact mobius_conjugate_fixedpoint h q w (hfix h hh)
  have hKno : ∀ f ∈ K, ¬Mobius.MobiusElliptic f := by
    rintro f ⟨h, hh, rfl⟩
    change ¬Mobius.MobiusElliptic (q * h * q⁻¹)
    rw [Mobius.mobiusElliptic_conjugation]
    exact hno h hh
  let : IsCyclic K := discrete_dilation_no_elliptics_isCyclic K hKd hKi hKz hKno
  exact (DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).isCyclic.mpr inferInstance

/-- Genuine common invariant discs survive arbitrary actual subgroup conjugation. -/
theorem invariantDisc_conjugate (H : Subgroup Mobius.complexMobiusGroup)
    (q : Mobius.complexMobiusGroup) (h : Mobius.HasInvariantComplexDisc H) :
    Mobius.HasInvariantComplexDisc (DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  obtain ⟨D, hD, hp⟩ := h
  refine ⟨q.val '' D, hD.image q, ?_⟩
  intro f
  obtain ⟨g, hg, hgf⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
  rw [← hgf, Set.image_image]
  change (fun z => q.val (g.val (q.val.symm (q.val z)))) '' D = q.val '' D
  simp only [Equiv.symm_apply_apply]
  rw [← Set.image_image, hp ⟨g, hg⟩]

theorem fuchsian_unitTranslation_eq_standard : mobiusTranslation 1 = Mobius.mobiusStandardElement 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rw [mobiusTranslation_infty, Mobius.mobiusStandardElement_infty]
  | coe z => simp [mobiusTranslation_coe, Mobius.mobiusStandardElement_coe]

theorem fuchsian_standardTranslation_fixed (z : Mobius.ExtendedComplex)
    (hz : (Mobius.mobiusStandardElement 1).val z = z) : z = ∞ := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z => simp [Mobius.mobiusStandardElement_coe] at hz

/-- A parabolic-containing discrete disc group with a common fixed point and no elliptics is cyclic. -/
theorem discrete_parabolic_common_fixed_cyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hD : Mobius.HasInvariantComplexDisc H)
    (w : Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val w = w)
    (p : Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp : Mobius.MobiusParabolic p)
    (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f) : IsCyclic H := by
  obtain ⟨q, hq⟩ := isConj_iff.mp ((Mobius.mobiusBoundaryParabolic_iff_conjugate_translation p hp.1).mp hp)
  have hqw : q.val w = ∞ := fuchsian_standardTranslation_fixed _ (by
    rw [← hq]
    exact mobius_conjugate_fixedpoint p q w (hfix p hpH))
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let : DiscreteTopology H := hd
  have hKd : Mobius.IsDiscreteMobiusSubgroup K := DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hKi : K ≤ Mobius.mobiusInftyStabilizer :=
    mobius_subgroupConjugate_le_inftyStabilizer H w (fun f => hfix f.val f.property) q hqw
  have hT1 : mobiusTranslation 1 ∈ K := by
    rw [fuchsian_unitTranslation_eq_standard, ← hq]
    exact ⟨p, hpH, rfl⟩
  have hKno : ∀ f ∈ K, ¬Mobius.MobiusElliptic f := by
    rintro f ⟨g, hg, rfl⟩
    change ¬Mobius.MobiusElliptic (q * g * q⁻¹)
    rw [Mobius.mobiusElliptic_conjugation]
    exact hno g hg
  have hKE : IsElementary K := isElementary_of_boundary_fixed K ∞ (fun f => hKi f.property)
  have hKnoL := discrete_elementary_parabolic_no_loxodromic K hKd hKE (mobiusTranslation 1)
    hT1 ((mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)
  obtain ⟨D, hdisc, hpres⟩ := invariantDisc_conjugate H q hD
  have hT : ∀ f ∈ K, ∃ r : ℝ, f = mobiusTranslation (r : ℂ) := by
    intro f hf
    let fi : Mobius.mobiusInftyStabilizer := ⟨f, hKi hf⟩
    have hm : Mobius.mobiusMultiplier fi = 1 := by
      by_cases h1 : f = 1
      · apply (mobiusMultiplier_eq_one_iff_parabolic_or_identity fi).mpr
        exact Or.inr h1
      · rcases Mobius.mobius_nonidentity_type_trichotomy f h1 with hp | hl | he
        · exact (mobiusMultiplier_eq_one_iff_parabolic_or_identity fi).mpr (Or.inl hp)
        · exact False.elim (hKnoL f hf hl)
        · exact False.elim (hKno f hf he)
    let b := Mobius.mobiusAffineConstant fi
    have hfb : f = mobiusTranslation b := by
      change fi.val = mobiusTranslation b
      rw [Mobius.mobius_affine_representation fi, hm]
      rfl
    have hb : b.im = 0 := Mobius.complexDisc_preserved_translation_im_eq_zero hdisc
      (hpres ⟨_, hT1⟩) (by rw [← hfb]; exact hpres ⟨f, hf⟩)
    have hbr : (b.re : ℂ) = b := Complex.ext (by simp) (by simpa using hb.symm)
    exact ⟨b.re, by rw [hbr]; exact hfb⟩
  let : IsCyclic K := discrete_real_translations_isCyclic K hKd hT
  exact (DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).isCyclic.mpr inferInstance

/-- Without nonidentity elliptics, an abelian actual Mobius subgroup has a common
boundary fixed point. The exceptional commuting involution configuration is excluded
by its genuine common interior fixed point. -/
theorem abelian_noElliptic_common_boundary_fixed (H : Subgroup Mobius.complexMobiusGroup)
    (hcomm : ∀ f g : H, Commute f g) (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f) :
    ∃ w : Mobius.ExtendedComplex, ∀ f ∈ H, f.val w = w := by
  classical
  by_cases htriv : ∀ f ∈ H, f = 1
  · exact ⟨∞, fun f hf => by rw [htriv f hf]; rfl⟩
  push Not at htriv
  obtain ⟨f, hf, hfn⟩ := htriv
  obtain ⟨w, hw⟩ := mobius_nonidentity_boundary_fixed_exists f hfn
  refine ⟨w, fun g hg => ?_⟩
  by_cases hgn : g = 1
  · subst g
    rfl
  have hc : Commute f g := congrArg Subtype.val (hcomm ⟨f, hf⟩ ⟨g, hg⟩).eq
  rcases (Mobius.mobius_commute_iff_preserves_fixed_points_and_configuration f g hfn hgn).2.mp hc with hs | ⟨⟨q,
    hqf, _⟩, _⟩
  · exact (hs w).mp hw
  · exact (hno f hf ((Mobius.mobiusElliptic_iff_H3_fixed f hfn).mpr ⟨q, hqf⟩)).elim

/-- Every discrete abelian subgroup preserving an actual disc and containing no
nonidentity elliptics is cyclic. No surface or chosen quotient model is assumed. -/
theorem discrete_abelian_noElliptic_invariantDisc_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hD : Mobius.HasInvariantComplexDisc H)
    (hcomm : ∀ f g : H, Commute f g) (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f) :
    IsCyclic H := by
  classical
  by_cases htriv : ∀ f ∈ H, f = 1
  · have hb : H = ⊥ := le_antisymm (fun f hf => Subgroup.mem_bot.mpr (htriv f hf)) bot_le
    subst H
    infer_instance
  push Not at htriv
  obtain ⟨g, hg, hgn⟩ := htriv
  obtain ⟨w, hw⟩ := abelian_noElliptic_common_boundary_fixed H hcomm hno
  rcases Mobius.mobius_nonidentity_type_trichotomy g hgn with hp | hl | he
  · exact discrete_parabolic_common_fixed_cyclic H hd hD w hw g hg hp hno
  · exact discrete_loxodromic_common_fixed_cyclic H hd w hw g hg hl hno
  · exact (hno g hg he).elim

end LowDimensionalTopology.Geometry.DiscreteGroups
