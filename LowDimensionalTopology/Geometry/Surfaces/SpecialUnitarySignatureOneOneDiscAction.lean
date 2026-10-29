/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.SpecialUnitarySignatureOneOneShape
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticAutomorphismGroup
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# PSU(1,1) as the original inherited-disc automorphism group

The normalized-shape producer supplies the disc preservation of every genuine
J-preserving matrix. Restriction uses the original sphere action and the same
inherited analytic atlas. The sign quotient is the original SU(1,1) quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped MatrixGroups ComplexConjugate

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The explicit normalized matrix condition gives genuine global disc preservation. -/
theorem specialLinear_normalized_shape_preserves_disc (A : SL(2, ℂ))
    (hshape : A 0 1 = conj (A 1 0) ∧ A 1 1 = conj (A 0 0) ∧
      Complex.normSq (A 0 0) - Complex.normSq (A 1 0) = 1) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) ''
      extendedUnitDisc = extendedUnitDisc := by
  obtain ⟨hb, hd, hdet⟩ := hshape
  have he : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) =
      normalizedDiscTransformation (A 0 0) (A 1 0) hdet := by
    have haction : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) =
        fractionalLinear (Matrix.SpecialLinearGroup.toGL A) := mobiusMatrixProjection_coe _
    rw [haction]
    apply congrArg fractionalLinear
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coefficientMatrix, hb, hd]
  rw [he]
  exact normalizedDiscTransformation_preserves_disc (A 0 0) (A 1 0) hdet

/-- The algebraic shape theorem removes every extra preservation hypothesis. -/
theorem specialUnitarySignatureOneOneProjection_preserves_disc
    (A : specialUnitarySignatureOneOne) :
    (specialUnitarySignatureOneOneProjection A : Equiv.Perm ExtendedComplex) ''
      extendedUnitDisc = extendedUnitDisc :=
  specialLinear_normalized_shape_preserves_disc A.val
    (specialUnitarySignatureOneOne_normalized_shape A.val A.property)

/-- Restriction of the original actual sphere homeomorphism to the original disc. -/
def specialUnitarySignatureOneOneDiscHomeomorph (A : specialUnitarySignatureOneOne) :
    extendedUnitDisc ≃ₜ extendedUnitDisc :=
  (mobiusBoundaryHomeomorph (specialUnitarySignatureOneOneProjection A)).subtype (by
    intro z
    change z ∈ extendedUnitDisc ↔
      (specialUnitarySignatureOneOneProjection A).val z ∈ extendedUnitDisc
    have hD := specialUnitarySignatureOneOneProjection_preserves_disc A
    constructor
    · intro hz
      rw [← hD]
      exact Set.mem_image_of_mem _ hz
    · intro hz
      rw [← hD] at hz
      obtain ⟨w, hw, he⟩ := hz
      exact (specialUnitarySignatureOneOneProjection A).val.injective he ▸ hw)

theorem specialUnitarySignatureOneOneDiscHomeomorph_coe
    (A : specialUnitarySignatureOneOne) (z : extendedUnitDisc) :
    (specialUnitarySignatureOneOneDiscHomeomorph A z).val =
      (specialUnitarySignatureOneOneProjection A).val z.val := rfl

/-- Analyticity is in the same inherited atlas as the original disk automorphisms. -/
theorem specialUnitarySignatureOneOneDiscHomeomorph_analytic
    (A : specialUnitarySignatureOneOne) :
    RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas (specialUnitarySignatureOneOneDiscHomeomorph A) := by
  exact RiemannAnalyticMap.liftLocalHomeomorph
    (Subtype.val : extendedUnitDisc → ExtendedComplex)
    (Subtype.val : extendedUnitDisc → ExtendedComplex)
    isOpen_extendedUnitDisc.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    isOpen_extendedUnitDisc.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (specialUnitarySignatureOneOneProjection A).val
    (specialUnitarySignatureOneOneDiscHomeomorph A)
    (mobius_riemannSphere_analytic (specialUnitarySignatureOneOneProjection A))
    (specialUnitarySignatureOneOneDiscHomeomorph A).continuous (fun _ => rfl)

/-- The original SU(1,1) action in the full actual analytic disc automorphism group. -/
def specialUnitarySignatureOneOneDiscAutHom : specialUnitarySignatureOneOne →*
    discRiemannSurface.toRiemannAtlas.analyticAutomorphismSubgroup where
  toFun A := ⟨specialUnitarySignatureOneOneDiscHomeomorph A,
    specialUnitarySignatureOneOneDiscHomeomorph_analytic A⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply Subtype.ext
    change (specialUnitarySignatureOneOneProjection 1).val z.val = z.val
    rw [map_one]
    rfl
  map_mul' A B := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply Subtype.ext
    change (specialUnitarySignatureOneOneProjection (A * B)).val z.val =
      (specialUnitarySignatureOneOneProjection A).val
        ((specialUnitarySignatureOneOneProjection B).val z.val)
    rw [map_mul]
    rfl

theorem specialUnitarySignatureOneOneDiscAutHom_apply
    (A : specialUnitarySignatureOneOne) (z : extendedUnitDisc) :
    ((specialUnitarySignatureOneOneDiscAutHom A).val z).val =
      (specialUnitarySignatureOneOneProjection A).val z.val := rfl

/-- Full surjectivity uses the original analytic-automorphism lift, not an action premise. -/
theorem specialUnitarySignatureOneOneDiscAutHom_surjective :
    Function.Surjective specialUnitarySignatureOneOneDiscAutHom := by
  intro H
  obtain ⟨A, hA⟩ := disc_analytic_automorphism_exists_specialUnitarySignatureOneOne H.val H.property
  refine ⟨A, Subtype.ext (Homeomorph.ext fun z => ?_)⟩
  exact Subtype.ext (hA z)

/-- Equality on the whole original disc detects precisely the original sign kernel. -/
theorem specialUnitarySignatureOneOneDiscAutHom_kernel :
    specialUnitarySignatureOneOneDiscAutHom.ker = specialUnitarySignatureOneOneSigns := by
  ext A
  change specialUnitarySignatureOneOneDiscAutHom A = 1 ↔
    A ∈ specialUnitarySignatureOneOneSigns
  rw [← specialUnitarySignatureOneOneProjection_kernel, MonoidHom.mem_ker]
  constructor
  · intro hA
    apply mobius_eq_of_agree_extendedUnitDisc
    intro z
    change (specialUnitarySignatureOneOneProjection A).val z.val = z.val
    exact congrArg
      (fun H : discRiemannSurface.toRiemannAtlas.analyticAutomorphismSubgroup =>
        (H.val z).val) hA
  · intro hA
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply Subtype.ext
    change (specialUnitarySignatureOneOneProjection A).val z.val = z.val
    rw [hA]
    rfl

/-- The source PSU(1,1) sign quotient is the full original inherited-disc Aut group. -/
def projectiveSpecialUnitarySignatureOneOneDiscAutEquiv :
    ProjectiveSpecialUnitarySignatureOneOne ≃*
      discRiemannSurface.toRiemannAtlas.analyticAutomorphismSubgroup :=
  QuotientGroup.liftEquiv specialUnitarySignatureOneOneSigns
    specialUnitarySignatureOneOneDiscAutHom_surjective
    specialUnitarySignatureOneOneDiscAutHom_kernel.symm

theorem projectiveSpecialUnitarySignatureOneOneDiscAutEquiv_mk
    (A : specialUnitarySignatureOneOne) :
    projectiveSpecialUnitarySignatureOneOneDiscAutEquiv (QuotientGroup.mk A) =
      specialUnitarySignatureOneOneDiscAutHom A :=
  QuotientGroup.liftEquiv_mk _ _ _ A

/-- The identified projective action agrees with the same original global sphere map. -/
theorem projectiveSpecialUnitarySignatureOneOneDiscAutEquiv_mk_apply
    (A : specialUnitarySignatureOneOne) (z : extendedUnitDisc) :
    ((projectiveSpecialUnitarySignatureOneOneDiscAutEquiv (QuotientGroup.mk A)).val z).val =
      (specialUnitarySignatureOneOneProjection A).val z.val := by
  rw [projectiveSpecialUnitarySignatureOneOneDiscAutEquiv_mk]
  rfl

end LowDimensionalTopology.Geometry.Surfaces
