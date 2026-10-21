/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sequences

/-!
Discrete matrix subgroups, their convergence criteria, and the integer-matrix
examples. All matrix norms below are the Frobenius norm.
-/

@[expose] public section

open Filter Topology
open scoped Matrix.Norms.Frobenius

namespace LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

/-- discreteness is discreteness of the subgroup topology. -/
abbrev DiscreteMatrixSubgroup (K : Subgroup Auxiliary.Algebra.GeneralLinear2) : Prop := DiscreteTopology K

section TopologicalGroups

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- one isolated subgroup point is enough for discreteness. -/
theorem discrete_of_isolated_point (K : Subgroup G) (x : K)
    (hx : IsOpen ({x} : Set K)) : DiscreteTopology K :=
  (MulAction.IsPretransitive.discreteTopology_iff K x).mpr hx

/-- A convergent sequence in a discrete subgroup stabilizes, even when the limit
was initially given only as a point of the ambient group. -/
theorem discrete_sequence_eventually_eq [T1Space G] (K : Subgroup G) [DiscreteTopology K]
    (u : ℕ → K) (x : G) (hu : Tendsto (fun n => (u n : G)) atTop (𝓝 x)) :
    ∀ᶠ n in atTop, (u n : G) = x := by
  have hx : x ∈ K := K.isClosed_of_discreteTopology.mem_of_tendsto hu
    (Eventually.of_forall fun n => (u n).property)
  have hu' : Tendsto u atTop (𝓝 (⟨x, hx⟩ : K)) :=
    Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu
  have h := hu'.eventually ((isOpen_discrete ({⟨x, hx⟩} : Set K)).mem_nhds (by simp))
  exact h.mono fun n hn => congrArg Subtype.val (Set.mem_singleton_iff.mp hn)

/-- sequences tending to the identity characterize discreteness. -/
theorem discrete_iff_identity_sequences [FirstCountableTopology G] (K : Subgroup G) :
    DiscreteTopology K ↔
      ∀ u : ℕ → K, Tendsto (fun n => (u n : G)) atTop (𝓝 (1 : G)) →
        ∀ᶠ n in atTop, u n = 1 := by
  constructor
  · intro h u hu
    let := h
    have hu' : Tendsto u atTop (𝓝 (1 : K)) :=
      Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu
    exact hu'.eventually ((isOpen_discrete ({1} : Set K)).mem_nhds (by simp))
  · intro h
    let _ : FirstCountableTopology K := Topology.IsEmbedding.subtypeVal.firstCountableTopology
    apply discreteTopology_of_isOpen_singleton_one
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hx' : x = (1 : K) := Set.mem_singleton_iff.mp hx
    subst x
    change ∀ᶠ x : K in 𝓝 (1 : K), x = 1
    exact (eventually_iff_seq_eventually (l := 𝓝 (1 : K))).mpr fun u hu =>
      h u ((continuous_subtype_val.tendsto (1 : K)).comp hu)

omit [IsTopologicalGroup G] in
/-- subgroups of discrete subgroups remain discrete. -/
theorem subgroup_discrete {K L : Subgroup G} [DiscreteTopology L] (hKL : K ≤ L) :
    DiscreteTopology K :=
  (Topology.IsEmbedding.inclusion hKL).discreteTopology

/-- fixed-element conjugation is a homeomorphism. -/
def conjugationHomeomorph (B : G) : G ≃ₜ G :=
  (Homeomorph.mulLeft B).trans (Homeomorph.mulRight B⁻¹)

theorem conjugationHomeomorph_apply (B A : G) :
    conjugationHomeomorph B A = B * A * B⁻¹ := rfl

/-- The conjugate subgroup is the image under the corresponding inner automorphism. -/
def conjugateSubgroup (B : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj B)

/-- conjugation preserves discreteness. -/
theorem conjugateSubgroup_discrete (B : G) (K : Subgroup G) [DiscreteTopology K] :
    DiscreteTopology (conjugateSubgroup B K) := by
  apply isDiscrete_iff_discreteTopology.mp
  have hK : IsDiscrete (K : Set G) := isDiscrete_iff_discreteTopology.mpr inferInstance
  exact hK.image (conjugationHomeomorph B).isEmbedding.isInducing

end TopologicalGroups

/-- The stabilization assertion with convergence stated in the ambient matrix space. -/
theorem matrix_discrete_sequence_eventually_eq (K : Subgroup Auxiliary.Algebra.GeneralLinear2)
    [DiscreteTopology K] (u : ℕ → K) (X : Auxiliary.Algebra.GeneralLinear2)
    (hu : Tendsto (fun n => ((u n).val : Auxiliary.Algebra.ComplexMatrix2)) atTop
      (𝓝 (X : Auxiliary.Algebra.ComplexMatrix2))) :
    ∀ᶠ n in atTop, ((u n).val : Auxiliary.Algebra.ComplexMatrix2) = (X : Auxiliary.Algebra.ComplexMatrix2) := by
  have hu' : Tendsto (fun n => (u n).val) atTop (𝓝 X) :=
    Auxiliary.Algebra.generalLinear_val_isEmbedding.tendsto_nhds_iff.mpr hu
  exact (discrete_sequence_eventually_eq K u X hu').mono fun n hn =>
    congrArg (fun A : Auxiliary.Algebra.GeneralLinear2 => (A : Auxiliary.Algebra.ComplexMatrix2)) hn

/-- The identity-sequence criterion in the geometric ambient matrix topology. -/
theorem discrete_iff_identity_matrix_sequences (K : Subgroup Auxiliary.Algebra.GeneralLinear2) :
    DiscreteTopology K ↔
      ∀ u : ℕ → K, Tendsto (fun n => ((u n).val : Auxiliary.Algebra.ComplexMatrix2)) atTop
        (𝓝 (1 : Auxiliary.Algebra.ComplexMatrix2)) → ∀ᶠ n in atTop, u n = 1 := by
  let _ : FirstCountableTopology Auxiliary.Algebra.ComplexMatrix2 :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℂ))
  let _ : FirstCountableTopology Auxiliary.Algebra.GeneralLinear2 :=
    Auxiliary.Algebra.generalLinear_val_isEmbedding.firstCountableTopology
  constructor
  · intro h u hu
    exact (discrete_iff_identity_sequences K).mp h u
      (Auxiliary.Algebra.generalLinear_val_isEmbedding.tendsto_nhds_iff.mpr hu)
  · intro h
    apply (discrete_iff_identity_sequences K).mpr
    intro u hu
    exact h u (Auxiliary.Algebra.generalLinear_val_isEmbedding.tendsto_nhds_iff.mp hu)

/--
A positive Frobenius distance gap at the identity implies discreteness.
The uniform-bound formulation also covers the trivial subgroup without an empty infimum.
-/
theorem discrete_of_identity_norm_gap (K : Subgroup Auxiliary.Algebra.GeneralLinear2)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ A : K, A ≠ 1 → ε ≤ Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.ComplexMatrix2) - 1)) :
    DiscreteTopology K := by
  apply discreteTopology_of_isOpen_singleton_one
  have hc : Continuous (fun A : K => Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.ComplexMatrix2) - 1)) :=
    Auxiliary.Algebra.matrixNorm_continuous.comp ((Units.continuous_val.comp continuous_subtype_val).sub
      continuous_const)
  have hset : {A : K | Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.ComplexMatrix2) - 1) < ε} = {1} := by
    ext A
    constructor
    · intro hA
      by_contra hA'
      exact (not_lt_of_ge (hgap A hA')) hA
    · intro hA
      have : A = 1 := hA
      subst A
      simpa [Auxiliary.Algebra.matrixNorm] using hε
  rw [← hset]
  exact isOpen_lt hc continuous_const

/-- The stated positive-infimum criterion. -/
theorem discrete_of_positive_identity_infimum (K : Subgroup Auxiliary.Algebra.GeneralLinear2)
    (hgap : 0 < sInf {r : ℝ | ∃ A : K, A ≠ 1 ∧
      r = Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.ComplexMatrix2) - 1)}) : DiscreteTopology K := by
  apply discrete_of_identity_norm_gap K _ hgap
  intro A hA
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨B, _, rfl⟩
    exact Auxiliary.Algebra.matrixNorm_nonneg _
  · exact ⟨A, hA, rfl⟩

/-- Norm-bounded parts of a discrete special-linear subgroup are finite. -/
theorem finite_norm_bounded (K : Subgroup Auxiliary.Algebra.SpecialLinear2) [DiscreteTopology K] (r : ℝ) :
    {A : K | Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2) ≤ r}.Finite := by
  have he : IsClosedEmbedding (fun A : K => ((A.val : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.ComplexMatrix2)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.comp
      K.isClosed_of_discreteTopology.isClosedEmbedding_subtypeVal
  simpa [Auxiliary.Algebra.matrixNorm, Metric.closedBall, dist_eq_norm] using
    (he.isCompact_preimage (isCompact_closedBall (0 : Auxiliary.Algebra.ComplexMatrix2) r)).finite_of_discrete

/-- equation: bounded-part finiteness characterizes discreteness in SL. -/
theorem discrete_iff_finite_norm_bounded (K : Subgroup Auxiliary.Algebra.SpecialLinear2) :
    DiscreteTopology K ↔
      ∀ r : ℝ, 0 < r →
        {A : K | Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
          Auxiliary.Algebra.ComplexMatrix2) ≤ r}.Finite := by
  constructor
  · intro h r _
    let := h
    exact finite_norm_bounded K r
  · intro h
    apply discreteTopology_of_isOpen_singleton_one
    let r := Auxiliary.Algebra.matrixNorm (1 : Auxiliary.Algebra.ComplexMatrix2) + 1
    have hr : 0 < r := by
      dsimp [r]
      linarith [Auxiliary.Algebra.matrixNorm_nonneg (1 : Auxiliary.Algebra.ComplexMatrix2)]
    have hc : Continuous (fun A : K => Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2)) :=
      Auxiliary.Algebra.matrixNorm_continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hn : {A : K | Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2) ≤ r} ∈
        𝓝 (1 : K) := by
      apply mem_of_superset ((hc.tendsto (1 : K)).eventually (Iio_mem_nhds ?_))
      · exact fun A hA => le_of_lt hA
      · change Auxiliary.Algebra.matrixNorm (1 : Auxiliary.Algebra.ComplexMatrix2) < Auxiliary.Algebra.matrixNorm
          (1 : Auxiliary.Algebra.ComplexMatrix2) + 1
        linarith
    exact isOpen_singleton_of_finite_mem_nhds (1 : K) hn (h r hr)

/-- discrete subgroups of SL(2,C) are countable. -/
theorem discrete_specialLinear_countable (K : Subgroup Auxiliary.Algebra.SpecialLinear2) [DiscreteTopology K] :
    Countable K := by
  have hcover : (⋃ n : ℕ,
      {A : K | Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
        Auxiliary.Algebra.ComplexMatrix2) ≤ (n : ℝ)}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro A
    obtain ⟨n, hn⟩ := exists_nat_ge (Auxiliary.Algebra.matrixNorm ((A.val : Auxiliary.Algebra.SpecialLinear2) :
      Auxiliary.Algebra.ComplexMatrix2))
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hc := Set.countable_iUnion fun n : ℕ => (finite_norm_bounded K (n : ℝ)).countable
  rw [hcover] at hc
  exact Set.countable_univ_iff.mp hc

/-- Injective coefficient maps identify the image subgroup with its entrywise description. -/
theorem mem_specialLinear_map_range_iff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (A : Matrix.SpecialLinearGroup (Fin 2) S) :
    A ∈ (Matrix.SpecialLinearGroup.map (n := Fin 2) f).range ↔
      ∀ i j, A i j ∈ Set.range f := by
  classical
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact ⟨B i j, rfl⟩
  · intro h
    choose B hB using h
    let B' : Matrix (Fin 2) (Fin 2) R := Matrix.of B
    have hmap : f.mapMatrix B' = (A : Matrix (Fin 2) (Fin 2) S) := by
      ext i j
      exact hB i j
    have hdet : Matrix.det B' = 1 := by
      apply hf
      rw [f.map_one, f.map_det, hmap]
      exact A.property
    refine ⟨⟨B', hdet⟩, ?_⟩
    apply Subtype.ext
    exact hmap

/-- The matrix modular group, before any projective quotient. -/
def modularGroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range

/-- The modular example consists of exactly the determinant-one integer-entry matrices. -/
theorem mem_modularGroup_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    A ∈ modularGroup ↔ ∀ i j, ∃ n : ℤ, (n : ℝ) = A i j :=
  mem_specialLinear_map_range_iff (Int.castRingHom ℝ) Int.cast_injective A

/-- The modular matrix group is discrete. -/
theorem modularGroup_discrete : DiscreteTopology modularGroup := by
  apply isDiscrete_iff_discreteTopology.mp
  exact Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.specialLinearGroup_map.isDiscrete_range

/-- Picard's matrix group uses Gaussian integer entries. -/
def picardGroup : Subgroup Auxiliary.Algebra.SpecialLinear2 :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) GaussianInt.toComplex).range

/-- The Picard example consists of exactly the Gaussian-integer-entry matrices. -/
theorem mem_picardGroup_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    A ∈ picardGroup ↔ ∀ i j, ∃ z : GaussianInt, (z : ℂ) = A i j :=
  mem_specialLinear_map_range_iff GaussianInt.toComplex GaussianInt.toComplex_injective A

/-- Picard's matrix group is discrete. -/
theorem picardGroup_discrete : DiscreteTopology picardGroup := by
  let _ : TopologicalSpace GaussianInt := ⊥
  let _ : DiscreteTopology GaussianInt := ⟨rfl⟩
  let coordinates : GaussianInt ≃ₜ ℤ × ℤ :=
    ({ toFun := fun z => (z.re, z.im)
       invFun := fun z => ⟨z.1, z.2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : GaussianInt ≃ ℤ × ℤ).toHomeomorphOfDiscrete
  have hcoord : IsEmbedding (fun z : GaussianInt => ((z.re : ℝ), (z.im : ℝ))) :=
    (Int.isClosedEmbedding_coe_real.isEmbedding.prodMap
      Int.isClosedEmbedding_coe_real.isEmbedding).comp coordinates.isEmbedding
  have he : IsEmbedding GaussianInt.toComplex := by
    apply IsEmbedding.of_comp continuous_of_discreteTopology Complex.equivRealProdCLM.continuous
    change IsEmbedding (fun z : GaussianInt => ((z : ℂ).re, (z : ℂ).im))
    simpa only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] using hcoord
  exact isDiscrete_iff_discreteTopology.mp he.isInducing.specialLinearGroup_map.isDiscrete_range

end LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups
