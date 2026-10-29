module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalDeck
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Actual canonically marked deck generators and nonzero matrix coefficients

The literal ordered surface presentation is transported from the original
closed surface to the deck group of its same half-plane covering. The inverse
of endpoint monodromy compensates for Mathlib's opposite-group convention.
Actual matrix representatives are obtained separately from the covering orbit
condition; no faithful lift of the whole deck group to SL(2,R) is assumed.

Every generator in this ordered marking other than the final b-generator
fails to commute with that generator. Consequently its matrix representative
has both off-diagonal entries nonzero whenever the final generator is diagonal.
The normalized geometric marking and the entire Fricke model are not defined
by this necessary bridge.

The literal surface presentation, free-generator noncommutation, last-handle
commutator quotient, triangular trace formulas and pure hyperbolicity theorem
are reused from Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane commutatorElement

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The final handle index in the actual genus-g presentation. -/
def finalHandle {g : ℕ} (hg : 1 < g) : Fin g := ⟨g - 1, by omega⟩

private def surfacePresentationHom {g : ℕ} {H : Type*} [Group H]
    (f : Fin g ⊕ Fin g → H)
    (hf : ∀ i : Fin g,
      f (Sum.inl i) * f (Sum.inr i) * (f (Sum.inl i))⁻¹ * (f (Sum.inr i))⁻¹ = 1) :
    LiZhongQC.surfaceGroup g →* H := by
  have hrel : ∀ r ∈ ({(List.ofFn fun i : Fin g =>
      FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
        (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod} :
      Set (FreeGroup (Fin g ⊕ Fin g))), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    rw [map_list_prod, List.map_ofFn]
    apply List.prod_eq_one
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    rw [← hi]
    simpa only [Function.comp_apply, map_mul, map_inv, FreeGroup.lift_apply_of] using hf i
  exact PresentedGroup.toGroup hrel

private theorem surfacePresentationHom_of {g : ℕ} {H : Type*} [Group H]
    (f : Fin g ⊕ Fin g → H)
    (hf : ∀ i : Fin g,
      f (Sum.inl i) * f (Sum.inr i) * (f (Sum.inl i))⁻¹ * (f (Sum.inr i))⁻¹ = 1)
    (s : Fin g ⊕ Fin g) :
    surfacePresentationHom f hf (PresentedGroup.of s) = f s := by
  unfold surfacePresentationHom
  exact PresentedGroup.toGroup.of _

private theorem surface_a_ne_commute_b_of_ne {g : ℕ} (i j : Fin g) (hij : i ≠ j) :
    ¬Commute (PresentedGroup.of (Sum.inl i) : LiZhongQC.surfaceGroup g)
      (PresentedGroup.of (Sum.inr j)) := by
  classical
  let f : Fin g ⊕ Fin g → FreeGroup (Fin 2) := Sum.elim
    (fun k => if k = i then FreeGroup.of 0 else 1)
    (fun k => if k = j then FreeGroup.of 1 else 1)
  have hf (k : Fin g) :
      f (Sum.inl k) * f (Sum.inr k) * (f (Sum.inl k))⁻¹ * (f (Sum.inr k))⁻¹ = 1 := by
    by_cases hki : k = i
    · subst k
      simp [f, hij]
    · simp [f, hki]
  let φ := surfacePresentationHom f hf
  have hφa : φ (PresentedGroup.of (Sum.inl i)) = FreeGroup.of (0 : Fin 2) := by
    simp [φ, surfacePresentationHom_of, f]
  have hφb : φ (PresentedGroup.of (Sum.inr j)) = FreeGroup.of (1 : Fin 2) := by
    simp [φ, surfacePresentationHom_of, f]
  intro h
  have he := h.map φ
  have hcomm : Commute (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2)) :=
    (congrArg₂ (fun a b : FreeGroup (Fin 2) => Commute a b) hφa hφb).mp he
  exact LiZhongQC.s22c2_free_two_generators_ne_commute hcomm.eq

private theorem surface_b_ne_commute_b_of_ne {g : ℕ} (i j : Fin g) (hij : i ≠ j) :
    ¬Commute (PresentedGroup.of (Sum.inr i) : LiZhongQC.surfaceGroup g)
      (PresentedGroup.of (Sum.inr j)) := by
  classical
  let f : Fin g ⊕ Fin g → FreeGroup (Fin 2) := Sum.elim (fun _ => 1)
    (fun k => if k = i then FreeGroup.of 0 else if k = j then FreeGroup.of 1 else 1)
  have hf (k : Fin g) :
      f (Sum.inl k) * f (Sum.inr k) * (f (Sum.inl k))⁻¹ * (f (Sum.inr k))⁻¹ = 1 := by
    simp [f]
  let φ := surfacePresentationHom f hf
  have hφa : φ (PresentedGroup.of (Sum.inr i)) = FreeGroup.of (0 : Fin 2) := by
    simp [φ, surfacePresentationHom_of, f]
  have hφb : φ (PresentedGroup.of (Sum.inr j)) = FreeGroup.of (1 : Fin 2) := by
    simp [φ, surfacePresentationHom_of, f, Ne.symm hij]
  intro h
  have he := h.map φ
  have hcomm : Commute (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2)) :=
    (congrArg₂ (fun a b : FreeGroup (Fin 2) => Commute a b) hφa hφb).mp he
  exact LiZhongQC.s22c2_free_two_generators_ne_commute hcomm.eq

/-- The entire ordered standard generator list, with its sole final-b exception,
has genuine noncommutation in the literal surface presentation. -/
theorem surface_generator_ne_commute_final_b {g : ℕ} (hg : 1 < g)
    (s : Fin g ⊕ Fin g) (hs : s ≠ Sum.inr (finalHandle hg)) :
    ¬Commute (PresentedGroup.of s : LiZhongQC.surfaceGroup g)
      (PresentedGroup.of (Sum.inr (finalHandle hg))) := by
  rcases s with i | i
  · by_cases hi : i = finalHandle hg
    · subst i
      intro h
      have hc : (PresentedGroup.of (Sum.inl (finalHandle hg)) : LiZhongQC.surfaceGroup g) *
          PresentedGroup.of (Sum.inr (finalHandle hg)) *
          (PresentedGroup.of (Sum.inl (finalHandle hg)))⁻¹ *
          (PresentedGroup.of (Sum.inr (finalHandle hg)))⁻¹ = 1 := by
        simpa only [commutatorElement_def] using h.commutator_eq
      have hsq : ((PresentedGroup.of (Sum.inl (finalHandle hg)) : LiZhongQC.surfaceGroup g) *
          PresentedGroup.of (Sum.inr (finalHandle hg)) *
          (PresentedGroup.of (Sum.inl (finalHandle hg)))⁻¹ *
          (PresentedGroup.of (Sum.inr (finalHandle hg)))⁻¹) ^ 2 = 1 :=
        (congrArg (fun c : LiZhongQC.surfaceGroup g => c ^ (2 : ℕ)) hc).trans (one_pow 2)
      exact LiZhongQC.s30e1_comm_sq_ne hg _ _ _ rfl rfl rfl hsq
    · exact surface_a_ne_commute_b_of_ne i (finalHandle hg) hi
  · exact surface_b_ne_commute_b_of_ne i (finalHandle hg) (fun hi => hs (congrArg Sum.inr hi))

/-- Both missing off-diagonal coefficients follow from the actual compact
uniformization and genuine noncommutation, rather than a faithful SL lift. -/
theorem offDiagonal_ne_zero_of_noncommuting_diagonal_deck
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : A ∈ Γ) (hD : D ∈ Γ)
    (hD01 : D 0 1 = 0) (hD10 : D 1 0 = 0) (hAD : ¬Commute A D) :
    A 0 1 ≠ 0 ∧ A 1 0 ≠ 0 := by
  have htrace_impossible
      (ht : LiZhongQC.slTrace (A * D * A⁻¹ * D⁻¹) = 2) : False := by
    let K := A * D * A⁻¹ * D⁻¹
    have hK : K ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hA hD)
      (Γ.inv_mem hA)) (Γ.inv_mem hD)
    have hK1 : K ≠ 1 := by
      intro he
      apply hAD
      exact commutatorElement_eq_one_iff_commute.mp
        (by simpa only [commutatorElement_def, K] using he)
    have hKm1 : K ≠ -1 := by
      intro he
      change LiZhongQC.slTrace K = 2 at ht
      rw [he] at ht
      norm_num [LiZhongQC.slTrace, Matrix.SpecialLinearGroup.coe_neg] at ht
    have hh := LiZhongQC.s27f_hyp hp hK hK1 hKm1
    change 2 < |LiZhongQC.slTrace K| at hh
    change LiZhongQC.slTrace K = 2 at ht
    rw [ht] at hh
    norm_num at hh
  exact ⟨fun hb => htrace_impossible (LiZhongQC.s30e1_comm_tr_lower hD01 hD10 hb),
    fun hc => htrace_impossible (LiZhongQC.s30e1_comm_tr_upper hD01 hD10 hc)⟩

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Teichmuller

variable {X : Type*} [TopologicalSpace X]

/-- Actual endpoint monodromy of the same original covering, with its genuine
opposite-group convention retained. -/
def ClosedRiemannSurface.surfaceDeckOppositeEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ) :
    LiZhongQC.surfaceGroup g ≃* (deck M.halfPlaneCover)ᵐᵒᵖ :=
  (R.surfaceGroupMulEquiv hgenus (M.halfPlaneCover z₀)).symm.trans
    ((covering_deck_isQuotientCoveringMap M.halfPlaneCover_covering
      M.halfPlaneCover_surjective).fundamentalGroupEquiv ⟨z₀, rfl⟩)

/-- Inverse endpoint monodromy gives an actual multiplicative deck marking of
the original surface presentation, without a chosen SL sign homomorphism. -/
def ClosedRiemannSurface.surfaceDeckEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ) :
    LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover :=
  (R.surfaceDeckOppositeEquiv hgenus M z₀).trans (MulEquiv.inv' (deck M.halfPlaneCover)).symm

/-- The algebraically ordered native handle generators on the original cover. -/
def ClosedRiemannSurface.canonicalDeckGenerator (R : ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ) (s : Fin g ⊕ Fin g) :
    deck M.halfPlaneCover :=
  R.surfaceDeckEquiv hgenus M z₀ (PresentedGroup.of s)

/-- The native ordered marking inherits the proved noncommutation of its
actual presentation; the final b-generator is the only exception. -/
theorem ClosedRiemannSurface.canonicalDeckGenerator_ne_commute_final_b
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ)
    (s : Fin g ⊕ Fin g) (hs : s ≠ Sum.inr (finalHandle hg)) :
    ¬Commute (R.canonicalDeckGenerator hgenus M z₀ s)
      (R.canonicalDeckGenerator hgenus M z₀ (Sum.inr (finalHandle hg))) := by
  intro h
  exact surface_generator_ne_commute_final_b hg s hs
    (Commute.of_map (R.surfaceDeckEquiv hgenus M z₀).injective h)

/-- Every true deck map is represented by a real determinant-one matrix in
the same uniformization; equality at one point extends by covering uniqueness. -/
theorem exists_uniformization_matrix_representative
    [ChartedSpace ℂ X] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → X} (hp : LiZhongQC.IsUniformization Γ p) (d : deck p) (z₀ : ℍ) :
    ∃ A ∈ Γ, ∀ z : ℍ, A • z = d • z := by
  obtain ⟨A, hA, hAz₀⟩ := (hp.2.2.2 z₀ (d • z₀)).mp (deck.proj_smul d z₀).symm
  refine ⟨A, hA, ?_⟩
  have hwhole : (fun z : ℍ => A • z) = (fun z : ℍ => d • z) := by
    apply hp.1.eq_of_comp_eq (continuous_const_smul A) (continuous_const_smul d) ?_ z₀ hAz₀
    funext z
    exact (LiZhongQC.s30a_p_smul hp hA z).trans (deck.proj_smul d z).symm
  exact fun z => congrFun hwhole z

/-- The actual ordered deck marking has matrix representatives on the given
original half-plane cover. This choice does not assert multiplicativity in SL. -/
theorem ClosedRiemannSurface.exists_canonicalDeck_matrix_representatives
    (R : ClosedRiemannSurface X) {g : ℕ} (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ) :
    ∃ A : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ s (z : ℍ), A s • z = R.canonicalDeckGenerator hgenus M z₀ s • z := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hrep (s : Fin g ⊕ Fin g) : ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℍ, A • z = R.canonicalDeckGenerator hgenus M z₀ s • z := by
    obtain ⟨A, _hA, he⟩ := exists_uniformization_matrix_representative hp
      (R.canonicalDeckGenerator hgenus M z₀ s) z₀
    exact ⟨A, he⟩
  choose A hA using hrep
  exact ⟨A, hA⟩

/-- A genuine marking of the actual covering deck group transfers the full
standard presentation. Its normalized generator matrices have both missing
coefficients nonzero; no homomorphism into SL itself is required. -/
theorem HyperbolicSurfaceModel.markedDeck_matrices_offDiagonal_ne_zero
    [CompactSpace X] {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    {g : ℕ} (hg : 1 < g) (ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover)
    (A : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ s (z : ℍ), A s • z = ρ (PresentedGroup.of s) • z)
    (hD01 : A (Sum.inr (finalHandle hg)) 0 1 = 0)
    (hD10 : A (Sum.inr (finalHandle hg)) 1 0 = 0)
    (s : Fin g ⊕ Fin g) (hs : s ≠ Sum.inr (finalHandle hg)) :
    A s 0 1 ≠ 0 ∧ A s 1 0 ≠ 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let t : Fin g ⊕ Fin g := Sum.inr (finalHandle hg)
  let D := A t
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hmem (u : Fin g ⊕ Fin g) : A u ∈ Γ := by
    apply (hΓ (A u)).mpr
    intro z
    rw [hA u z]
    exact deck.proj_smul (ρ (PresentedGroup.of u)) z
  have hAD : ¬Commute (A s) D := by
    intro h
    apply surface_generator_ne_commute_final_b hg s hs
    apply Commute.of_map ρ.injective
    change ρ (PresentedGroup.of s) * ρ (PresentedGroup.of t) =
      ρ (PresentedGroup.of t) * ρ (PresentedGroup.of s)
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    change ρ (PresentedGroup.of s) • (ρ (PresentedGroup.of t) • z) =
      ρ (PresentedGroup.of t) • (ρ (PresentedGroup.of s) • z)
    calc
      _ = A s • (A t • z) := by rw [← hA t z, ← hA s (A t • z)]
      _ = A t • (A s • z) := by
        simpa only [D, mul_smul] using congrArg (fun B => B • z) h.eq
      _ = _ := by rw [hA s z, hA t]
  exact offDiagonal_ne_zero_of_noncommuting_diagonal_deck hp (A s) D
    (hmem s) (hmem t) hD01 hD10 hAD

/-- The native same-surface deck marking is a genuine consumer of the marked
presentation theorem, with compactness supplied by the original closed surface. -/
theorem ClosedRiemannSurface.canonicalDeck_matrices_offDiagonal_ne_zero
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ)
    (A : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ s (z : ℍ), A s • z = R.canonicalDeckGenerator hgenus M z₀ s • z)
    (hD01 : A (Sum.inr (finalHandle hg)) 0 1 = 0)
    (hD10 : A (Sum.inr (finalHandle hg)) 1 0 = 0)
    (s : Fin g ⊕ Fin g) (hs : s ≠ Sum.inr (finalHandle hg)) :
    A s 0 1 ≠ 0 ∧ A s 1 0 ≠ 0 := by
  let := R.compactSpace
  exact M.markedDeck_matrices_offDiagonal_ne_zero hg (R.surfaceDeckEquiv hgenus M z₀)
    A hA hD01 hD10 s hs

/-- The full nonvanishing product for every actual normalized ordered
generator other than the final b-generator. -/
theorem ClosedRiemannSurface.canonicalDeck_matrices_bc_ne_zero
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (z₀ : ℍ)
    (A : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ s (z : ℍ), A s • z = R.canonicalDeckGenerator hgenus M z₀ s • z)
    (hD01 : A (Sum.inr (finalHandle hg)) 0 1 = 0)
    (hD10 : A (Sum.inr (finalHandle hg)) 1 0 = 0)
    (s : Fin g ⊕ Fin g) (hs : s ≠ Sum.inr (finalHandle hg)) :
    A s 0 1 * A s 1 0 ≠ 0 := by
  obtain ⟨hb, hc⟩ := R.canonicalDeck_matrices_offDiagonal_ne_zero hg hgenus M z₀ A hA
    hD01 hD10 s hs
  exact mul_ne_zero hb hc

end LowDimensionalTopology.Geometry.Surfaces
