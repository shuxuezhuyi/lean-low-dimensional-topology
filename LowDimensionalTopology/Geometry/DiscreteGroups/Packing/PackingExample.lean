/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.PackingFreeProducts
@[expose] public section
open Set Filter Monoid
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- Actual translations form the additive complex group inside the geometric Mobius group. -/
def packingTranslationHom : Multiplicative ℂ →* Mobius.complexMobiusGroup where
  toFun b := mobiusTranslation b.toAdd
  map_one' := (mobiusTranslation_eq_one_iff 0).mpr rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
      change (mobiusTranslation (a.toAdd + b.toAdd)).val ∞ =
        (mobiusTranslation a.toAdd).val ((mobiusTranslation b.toAdd).val ∞)
      simp only [mobiusTranslation_infty]
    | coe z =>
      change (mobiusTranslation (a.toAdd + b.toAdd)).val z =
        (mobiusTranslation a.toAdd).val ((mobiusTranslation b.toAdd).val z)
      simp only [mobiusTranslation_coe]
      congr 1
      ring

theorem packingTranslation_zpow (b : ℂ) (n : ℤ) :
    mobiusTranslation b ^ n = mobiusTranslation ((n : ℂ) * b) := by
  change (packingTranslationHom (Multiplicative.ofAdd b)) ^ n = _
  rw [← map_zpow]
  change mobiusTranslation ((Multiplicative.ofAdd b) ^ n).toAdd = _
  rw [toAdd_zpow]
  congr 1
  exact zsmul_eq_mul b n

/-- An actual finite vertical strip in the compactified complex plane. -/
def packingVerticalStrip (t : ℝ) : Set Mobius.ExtendedComplex :=
  OnePoint.some '' {z : ℂ | |z.re| < t / 2}

theorem coe_mem_packingVerticalStrip (t : ℝ) (z : ℂ) :
    (z : Mobius.ExtendedComplex) ∈ packingVerticalStrip t ↔ |z.re| < t / 2 := by
  simp [packingVerticalStrip]

theorem packingVerticalStrip_isOpen (t : ℝ) : IsOpen (packingVerticalStrip t) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_lt (Complex.continuous_re.abs) continuous_const)

theorem packingVerticalStrip_nonempty {t : ℝ} (ht : 0 < t) :
    (packingVerticalStrip t).Nonempty :=
  ⟨(0 : ℂ), (coe_mem_packingVerticalStrip t 0).mpr (by simpa using half_pos ht)⟩

theorem packingVerticalStrip_translation_packing {t : ℝ} (ht : 0 < t) :
    IsMobiusPacking (Subgroup.zpowers (mobiusTranslation (t : ℂ))) (packingVerticalStrip t) := by
  intro g hg
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    apply hg
    exact Subtype.ext hn.symm
  apply Set.disjoint_left.mpr
  rintro w ⟨v, hv, hgv⟩ hw
  obtain ⟨z, hz, rfl⟩ := hv
  rw [← hn, packingTranslation_zpow, mobiusTranslation_coe] at hgv
  have hmem : (((z + (n : ℂ) * t : ℂ)) : Mobius.ExtendedComplex) ∈ packingVerticalStrip t := hgv.symm ▸ hw
  have hz' := abs_lt.mp (show |z.re| < t / 2 from hz)
  have hw' := abs_lt.mp ((coe_mem_packingVerticalStrip t _).mp hmem)
  have hre : (z + (n : ℂ) * t).re = z.re + (n : ℝ) * t := by simp
  rw [hre] at hw'
  rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
  · have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hnneg
    nlinarith
  · have hnr : (1 : ℝ) ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr hnpos
    nlinarith

/-- Actual conjugation carries packing sets to packing sets. -/
theorem IsMobiusPacking.conjugation {H : Subgroup Mobius.complexMobiusGroup} {D : Set Mobius.ExtendedComplex}
    (hp : IsMobiusPacking H D) (q : Mobius.complexMobiusGroup) :
    IsMobiusPacking (DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val '' D) := by
  intro f hf
  obtain ⟨g, hg, hgf⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
  have hgne : g ≠ 1 := by
    intro he
    apply hf
    apply Subtype.ext
    rw [← hgf, he]
    simp
  have hgH : (⟨g, hg⟩ : H) ≠ 1 := fun he => hgne (congrArg Subtype.val he)
  have he : (q * g * q⁻¹).val '' (q.val '' D) = q.val '' (g.val '' D) := by
    simp only [Set.image_image]
    congr 1
    funext z
    change q.val (g.val (q.val.symm (q.val z))) = q.val (g.val z)
    rw [Equiv.symm_apply_apply]
  rw [← hgf, he]
  exact (Set.disjoint_image_iff q.val.injective).mpr (hp ⟨g, hg⟩ hgH)

/-- The two-disc exterior is the reciprocal image of the unit-width vertical strip. -/
def packingSecondDomain : Set Mobius.ExtendedComplex := Mobius.reciprocalMobius.val '' packingVerticalStrip 1

theorem mem_packingSecondDomain (z : Mobius.ExtendedComplex) :
    z ∈ packingSecondDomain ↔ Mobius.reciprocal z ∈ packingVerticalStrip 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change Mobius.reciprocal (Mobius.reciprocal w) ∈ packingVerticalStrip 1
    rw [Mobius.reciprocal_involutive]
    exact hw
  · intro hz
    exact ⟨Mobius.reciprocal z, hz, Mobius.reciprocal_involutive z⟩

theorem packing_inv_strip_circle_iff (z : ℂ) (hz : z ≠ 0) :
    |z⁻¹.re| < 1 / 2 ↔ 1 < ‖z + 1‖ ∧ 1 < ‖z - 1‖ := by
  have hn := Complex.normSq_pos.mpr hz
  have hp : ‖z + 1‖ ^ 2 = Complex.normSq z + 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hm : ‖z - 1‖ ^ 2 = Complex.normSq z - 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [Complex.inv_re, abs_lt]
  constructor
  · rintro ⟨ha, hb⟩
    have ha' := (lt_div_iff₀ hn).mp ha
    have hb' := (div_lt_iff₀ hn).mp hb
    constructor
    · apply (sq_lt_sq₀ zero_le_one (norm_nonneg (z + 1))).mp
      nlinarith
    · apply (sq_lt_sq₀ zero_le_one (norm_nonneg (z - 1))).mp
      nlinarith
  · rintro ⟨ha, hb⟩
    have ha' := (sq_lt_sq₀ zero_le_one (norm_nonneg (z + 1))).mpr ha
    have hb' := (sq_lt_sq₀ zero_le_one (norm_nonneg (z - 1))).mpr hb
    constructor
    · apply (lt_div_iff₀ hn).mpr
      nlinarith
    · apply (div_lt_iff₀ hn).mpr
      nlinarith

theorem coe_mem_packingSecondDomain (z : ℂ) :
    (z : Mobius.ExtendedComplex) ∈ packingSecondDomain ↔ 1 < ‖z + 1‖ ∧ 1 < ‖z - 1‖ := by
  rw [mem_packingSecondDomain]
  by_cases hz : z = 0
  · subst z
    simp [Mobius.reciprocal_zero, packingVerticalStrip]
  · rw [Mobius.reciprocal_coe z hz, coe_mem_packingVerticalStrip]
    exact packing_inv_strip_circle_iff z hz

theorem infty_mem_packingSecondDomain : ∞ ∈ packingSecondDomain := by
  rw [mem_packingSecondDomain, Mobius.reciprocal_infty, coe_mem_packingVerticalStrip]
  norm_num

theorem packing_reciprocal_inv : Mobius.reciprocalMobius⁻¹ = Mobius.reciprocalMobius := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  apply Mobius.reciprocal.injective
  change Mobius.reciprocal (Mobius.reciprocal.symm z) = Mobius.reciprocal (Mobius.reciprocal z)
  rw [Equiv.apply_symm_apply, Mobius.reciprocal_involutive]

/-- The second actual generator in the source's two-generator packing example. -/
def packingSecondGenerator : Mobius.complexMobiusGroup :=
  Mobius.reciprocalMobius * mobiusTranslation 1 * Mobius.reciprocalMobius⁻¹

theorem packingSecondGenerator_projection : packingSecondGenerator =
    Mobius.mobiusMatrixProjection (Mobius.coefficientMatrix 1 0 1 1 (by norm_num)) := by
  rw [packingSecondGenerator, packing_reciprocal_inv]
  change Mobius.mobiusMatrixProjection (Mobius.coefficientMatrix 0 1 1 0 (by norm_num)) *
    Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix 1 1) *
    Mobius.mobiusMatrixProjection (Mobius.coefficientMatrix 0 1 1 0 (by norm_num)) = _
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Mobius.coefficientMatrix, Mobius.Classification.affineMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem packingSecondGenerator_coe (z : ℂ) :
    packingSecondGenerator.val (z : Mobius.ExtendedComplex) =
      if z + 1 = 0 then ∞ else ((z / (z + 1) : ℂ) : Mobius.ExtendedComplex) := by
  rw [packingSecondGenerator_projection, Mobius.mobiusMatrixProjection_apply, Mobius.fractionalLinear_coe]
  change (if (1 : ℂ) * z + 1 = 0 then ∞ else
    ((((1 : ℂ) * z + 0) / ((1 : ℂ) * z + 1) : ℂ) : Mobius.ExtendedComplex)) = _
  simp only [one_mul, add_zero]

def packingFirstGroup : Subgroup Mobius.complexMobiusGroup := Subgroup.zpowers (mobiusTranslation 6)
def packingSecondGroup : Subgroup Mobius.complexMobiusGroup := Subgroup.zpowers packingSecondGenerator

theorem packingSecondGroup_conjugation : packingSecondGroup =
    DiscreteGroups.Action.Actions.subgroupConjugate Mobius.reciprocalMobius (Subgroup.zpowers (mobiusTranslation
      1)) := by
  rw [DiscreteGroups.Action.Actions.subgroupConjugate, MonoidHom.map_zpowers]
  rfl

theorem packingSecondDomain_isOpen : IsOpen packingSecondDomain :=
  (Mobius.mobiusBoundaryHomeomorph Mobius.reciprocalMobius).isOpenMap _ (packingVerticalStrip_isOpen 1)

theorem packingSecondDomain_isPacking : IsMobiusPacking packingSecondGroup packingSecondDomain := by
  rw [packingSecondGroup_conjugation]
  exact DiscreteGroups.IsMobiusPacking.conjugation (packingVerticalStrip_translation_packing (by norm_num))
    Mobius.reciprocalMobius

theorem packing_example_domains_cover : packingVerticalStrip 6 ∪ packingSecondDomain = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  induction z using OnePoint.rec with
  | infty => exact Or.inr infty_mem_packingSecondDomain
  | coe z =>
    by_cases h : |z.re| < 3
    · left
      exact (coe_mem_packingVerticalStrip 6 z).mpr (by norm_num; exact h)
    · right
      apply (coe_mem_packingSecondDomain z).mpr
      have h3 : 3 ≤ |z.re| := le_of_not_gt h
      have hp : |z.re + 1| ≤ ‖z + 1‖ := by simpa using Complex.abs_re_le_norm (z + 1)
      have hm : |z.re - 1| ≤ ‖z - 1‖ := by simpa using Complex.abs_re_le_norm (z - 1)
      by_cases hx : 0 ≤ z.re
      · rw [abs_of_nonneg hx] at h3
        have hp' := (le_abs_self (z.re + 1)).trans hp
        have hm' := (le_abs_self (z.re - 1)).trans hm
        constructor <;> linarith
      · rw [abs_of_neg (lt_of_not_ge hx)] at h3
        have hp' := (neg_le_abs (z.re + 1)).trans hp
        have hm' := (neg_le_abs (z.re - 1)).trans hm
        constructor <;> linarith

theorem packing_example_common_nonempty :
    (packingVerticalStrip 6 ∩ packingSecondDomain).Nonempty := by
  refine ⟨(Complex.I : ℂ), ?_, ?_⟩
  · rw [coe_mem_packingVerticalStrip]
    norm_num
  · rw [mem_packingSecondDomain, Mobius.reciprocal_coe Complex.I Complex.I_ne_zero,
      coe_mem_packingVerticalStrip]
    norm_num [Complex.inv_I]

/-- The actual two cyclic factors of the source example. -/
def packingExampleGroups : Bool → Subgroup Mobius.complexMobiusGroup
  | false => packingFirstGroup
  | true => packingSecondGroup

def packingExampleDomains : Bool → Set Mobius.ExtendedComplex
  | false => packingVerticalStrip 6
  | true => packingSecondDomain

theorem packingExampleDomains_packing (i : Bool) :
    IsMobiusPacking (packingExampleGroups i) (packingExampleDomains i) := by
  cases i with
  | false => exact packingVerticalStrip_translation_packing (by norm_num)
  | true => exact packingSecondDomain_isPacking

theorem packingExampleDomains_open (i : Bool) : IsOpen (packingExampleDomains i) := by
  cases i with
  | false => exact packingVerticalStrip_isOpen 6
  | true => exact packingSecondDomain_isOpen

theorem packingExampleDomains_cover (i j : Bool) (hij : i ≠ j) :
    packingExampleDomains i ∪ packingExampleDomains j = Set.univ := by
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact packing_example_domains_cover
  · change packingSecondDomain ∪ packingVerticalStrip 6 = Set.univ
    rw [Set.union_comm]
    exact packing_example_domains_cover
  · exact False.elim (hij rfl)

theorem packingExampleDomains_common_nonempty : (⋂ i, packingExampleDomains i).Nonempty := by
  obtain ⟨z, hz1, hz2⟩ := packing_example_common_nonempty
  refine ⟨z, Set.mem_iInter.mpr fun i => ?_⟩
  cases i
  · exact hz1
  · exact hz2

/-- The strip and reciprocal-strip generators form a free product with a discontinuous packing. -/
theorem mobius_packing_free_product_example :
    Nonempty (CoprodI (fun i => packingExampleGroups i) ≃*
      ↥(⨆ i, packingExampleGroups i : Subgroup Mobius.complexMobiusGroup)) ∧
      IsMobiusPacking (⨆ i, packingExampleGroups i) (⋂ i, packingExampleDomains i) ∧
      IsMobiusDiscontinuousOn (⨆ i, packingExampleGroups i)
        (mobiusSaturation (⨆ i, packingExampleGroups i) (⋂ i, packingExampleDomains i)) :=
  finite_packing_family_freeProduct_packing_discontinuity packingExampleGroups packingExampleDomains
    packingExampleDomains_open packingExampleDomains_packing packingExampleDomains_cover
    packingExampleDomains_common_nonempty

end
end LowDimensionalTopology.Geometry.DiscreteGroups
