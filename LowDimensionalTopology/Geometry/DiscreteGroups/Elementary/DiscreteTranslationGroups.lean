module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.Mobius
public import LowDimensionalTopology.Geometry.Euclidean.Lattice
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Set Filter
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- The actual translation representation of the additive complex plane. -/
def translationMobiusHom : Multiplicative ℂ →* Mobius.complexMobiusGroup where
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
      change (mobiusTranslation (a.toAdd + b.toAdd)).val (z : Mobius.ExtendedComplex) =
        (mobiusTranslation a.toAdd).val ((mobiusTranslation b.toAdd).val (z : Mobius.ExtendedComplex))
      rw [mobiusTranslation_coe, mobiusTranslation_coe, mobiusTranslation_coe]
      congr 1
      ring

theorem mobiusTranslation_add (a b : ℂ) :
    mobiusTranslation (a + b) = mobiusTranslation a * mobiusTranslation b :=
  translationMobiusHom.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

theorem mobiusTranslation_neg (a : ℂ) :
    mobiusTranslation (-a) = (mobiusTranslation a)⁻¹ :=
  translationMobiusHom.map_inv (Multiplicative.ofAdd a)

theorem mobiusTranslation_injective : Function.Injective mobiusTranslation := by
  intro a b hab
  have hzero := congrArg (fun f : Mobius.complexMobiusGroup => f.val ((0 : ℂ) : Mobius.ExtendedComplex)) hab
  simpa only [mobiusTranslation_coe, zero_add, OnePoint.coe_eq_coe] using hzero

/-- A canonical determinant-one lift of the actual translation. -/
def translationSpecialLinearMatrix (b : ℂ) : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem translationSpecialLinearMatrix_projection (b : ℂ) :
    Mobius.mobiusSpecialLinearProjection (translationSpecialLinearMatrix b) = mobiusTranslation b := by
  change Mobius.mobiusMatrixProjection (Matrix.SpecialLinearGroup.toGL (translationSpecialLinearMatrix b)) =
    Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix 1 b)
  apply congrArg Mobius.mobiusMatrixProjection
  apply Units.ext
  rfl

theorem mobiusTranslation_continuous : Continuous mobiusTranslation := by
  have hSL : Continuous translationSpecialLinearMatrix := by
    unfold translationSpecialLinearMatrix
    apply Continuous.subtype_mk
    fun_prop
  have h := Mobius.mobiusSpecialLinearProjection_continuous.comp hSL
  simpa only [Function.comp_def, translationSpecialLinearMatrix_projection] using h

/-- The displacement vectors of translations lying in an actual Mobius subgroup. -/
def translationDisplacements (H : Subgroup Mobius.complexMobiusGroup) : AddSubgroup ℂ where
  carrier := {b | mobiusTranslation b ∈ H}
  zero_mem' := by
    change mobiusTranslation 0 ∈ H
    rw [(mobiusTranslation_eq_one_iff 0).mpr rfl]
    exact H.one_mem
  add_mem' {a b} ha hb := by
    change mobiusTranslation (a + b) ∈ H
    rw [mobiusTranslation_add]
    exact H.mul_mem ha hb
  neg_mem' {a} ha := by
    change mobiusTranslation (-a) ∈ H
    rw [mobiusTranslation_neg]
    exact H.inv_mem ha

theorem mem_translationDisplacements (H : Subgroup Mobius.complexMobiusGroup) (b : ℂ) :
    b ∈ translationDisplacements H ↔ mobiusTranslation b ∈ H := Iff.rfl

/-- Discreteness is transported from the original Mobius topology by the actual continuous
injective translation representation. -/
theorem translationDisplacements_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) : DiscreteTopology (translationDisplacements H) := by
  let : DiscreteTopology H := hH
  change DiscreteTopology (mobiusTranslation ⁻¹' (H : Set Mobius.complexMobiusGroup))
  exact DiscreteTopology.preimage_of_continuous_injective (H : Set Mobius.complexMobiusGroup)
    mobiusTranslation_continuous mobiusTranslation_injective

/-- The translation vectors in every discrete actual Mobius subgroup have integer rank at most two,
with a real-linearly independent integer basis in the original complex plane. -/
theorem translationDisplacements_basis (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ v : Fin n → ℂ, LinearIndependent ℝ v ∧
      (translationDisplacements H : Set ℂ) = (Submodule.span ℤ (Set.range v) : Set ℂ) := by
  let : DiscreteTopology (translationDisplacements H) := translationDisplacements_discrete H hH
  have : DiscreteTopology (translationDisplacements H).toIntSubmodule :=
    (inferInstance : DiscreteTopology (translationDisplacements H))
  obtain ⟨n, hn, v, hv, hspan⟩ :=
    Euclidean.discrete_complex_submodule_basis (translationDisplacements H).toIntSubmodule
  exact ⟨n, hn, v, hv, congrArg SetLike.coe hspan⟩


/-- The actual translation map restricted to the displacement subgroup. -/
def translationDisplacementHom (H : Subgroup Mobius.complexMobiusGroup) :
    Multiplicative (translationDisplacements H) →* H where
  toFun b := ⟨mobiusTranslation b.toAdd.val, b.toAdd.property⟩
  map_one' := Subtype.ext ((mobiusTranslation_eq_one_iff 0).mpr rfl)
  map_mul' a b := Subtype.ext (mobiusTranslation_add a.toAdd.val b.toAdd.val)

theorem translationDisplacementHom_injective (H : Subgroup Mobius.complexMobiusGroup) :
    Function.Injective (translationDisplacementHom H) := by
  intro a b hab
  have hval := congrArg (fun g : H => g.val) hab
  have he : a.toAdd.val = b.toAdd.val := mobiusTranslation_injective hval
  exact Subtype.ext he

theorem translationDisplacementHom_surjective (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    Function.Surjective (translationDisplacementHom H) := by
  intro g
  obtain ⟨b, hb⟩ := hT g.val g.property
  have hbH : mobiusTranslation b ∈ H := by rw [← hb]; exact g.property
  exact ⟨Multiplicative.ofAdd (⟨b, hbH⟩ : translationDisplacements H), Subtype.ext hb.symm⟩

/-- A subgroup consisting entirely of actual translations is isomorphic to its additive displacement subgroup. -/
def translationDisplacementEquiv (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    Multiplicative (translationDisplacements H) ≃* H :=
  MulEquiv.ofBijective (translationDisplacementHom H)
    ⟨translationDisplacementHom_injective H, translationDisplacementHom_surjective H hT⟩

theorem translationDisplacementEquiv_apply (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b)
    (b : Multiplicative (translationDisplacements H)) :
    (translationDisplacementEquiv H hT b).val = mobiusTranslation b.toAdd.val := rfl

theorem translationDisplacementHom_continuous (H : Subgroup Mobius.complexMobiusGroup) :
    Continuous (translationDisplacementHom H) := by
  apply Continuous.subtype_mk
  exact mobiusTranslation_continuous.comp continuous_subtype_val

theorem translationDisplacementEquiv_continuous (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    Continuous (translationDisplacementEquiv H hT) :=
  translationDisplacementHom_continuous H

theorem translationDisplacementEquiv_symm_continuous (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    Continuous (translationDisplacementEquiv H hT).symm := by
  let e := translationDisplacementEquiv H hT
  change Continuous (fun g : H => (e.symm g).toAdd)
  apply continuous_induced_rng.mpr
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  have h : Continuous (fun g : H => g.val.val ((0 : ℂ) : Mobius.ExtendedComplex)) :=
    (Mobius.mobiusLocal_eval_continuous ((0 : ℂ) : Mobius.ExtendedComplex)).comp continuous_subtype_val
  convert h using 1
  funext g
  change (((e.symm g).toAdd.val : ℂ) : Mobius.ExtendedComplex) = g.val.val ((0 : ℂ) : Mobius.ExtendedComplex)
  have he : mobiusTranslation (e.symm g).toAdd.val = g.val :=
    congrArg (fun k : H => k.val) (e.apply_symm_apply g)
  have hv := congrArg (fun f : Mobius.complexMobiusGroup => f.val ((0 : ℂ) : Mobius.ExtendedComplex)) he
  simpa only [mobiusTranslation_coe, zero_add] using hv

/-- The group isomorphism uses exactly the original subspace topologies on both sides. -/
def translationDisplacementHomeomorph (H : Subgroup Mobius.complexMobiusGroup)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    Multiplicative (translationDisplacements H) ≃ₜ H where
  toEquiv := (translationDisplacementEquiv H hT).toEquiv
  continuous_toFun := translationDisplacementEquiv_continuous H hT
  continuous_invFun := translationDisplacementEquiv_symm_continuous H hT


/-- A discrete translation-only actual Mobius subgroup is generated by at most two
translations with real-linearly independent displacement vectors. The zero-rank case is retained. -/
theorem translationSubgroup_integer_basis (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H)
    (hT : ∀ g ∈ H, ∃ b : ℂ, g = mobiusTranslation b) :
    ∃ n : ℕ, n ≤ 2 ∧ ∃ v : Fin n → ℂ, LinearIndependent ℝ v ∧
      ∀ g : Mobius.complexMobiusGroup, g ∈ H ↔
        ∃ c : Fin n → ℤ, g = mobiusTranslation (∑ i, c i • v i) := by
  obtain ⟨n, hn, v, hv, hspan⟩ := translationDisplacements_basis H hH
  refine ⟨n, hn, v, hv, ?_⟩
  intro g
  constructor
  · intro hg
    obtain ⟨b, hb⟩ := hT g hg
    have hbL : b ∈ translationDisplacements H := by
      change mobiusTranslation b ∈ H
      rw [← hb]
      exact hg
    have hbspan : b ∈ Submodule.span ℤ (Set.range v) := by
      change b ∈ (Submodule.span ℤ (Set.range v) : Set ℂ)
      rw [← hspan]
      exact hbL
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hbspan
    exact ⟨c, hc ▸ hb⟩
  · rintro ⟨c, rfl⟩
    change (∑ i, c i • v i) ∈ translationDisplacements H
    change (∑ i, c i • v i) ∈ (translationDisplacements H : Set ℂ)
    rw [hspan]
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
