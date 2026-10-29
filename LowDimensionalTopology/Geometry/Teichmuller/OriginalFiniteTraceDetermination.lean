module

public import LowDimensionalTopology.Geometry.Teichmuller.FiniteBookTraceCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.FixedPointMatrixNormalization
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed

/-!
# The original normalized Fuchsian generator system is determined by finite traces

Both groups uniformize their actual original closed Riemann surfaces. The
only normalization assumptions are the original attracting and repelling
fixed points. Positive matrix representatives and nonzero traces are proved
internally. The finite observation set is the literal original one.
No standard generator marking, faithful determinant-one lift, extra trace
word, primitive-element condition or supplied finiteness conclusion is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set LiZhongQC
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The two distinguished transformations have the actual original endpoint
normalization, allowing the negative repelling point to be different in the
two systems being compared. -/
def FixedPointNormalizedPair {m : ℕ} (γ : Fin (m + 2) → TraceSL) : Prop :=
  attractingFixedPoint (γ 0) = extInf ∧
  repellingFixedPoint (γ 0) = ((0 : ℂ) : ExtPlane) ∧
  ∃ r : ℝ, r < 0 ∧ attractingFixedPoint (γ 1) = ((1 : ℂ) : ExtPlane) ∧
    repellingFixedPoint (γ 1) = ((r : ℂ) : ExtPlane)

private theorem noncentral_of_finite_repelling {A : TraceSL} {r : ℝ}
    (h : repellingFixedPoint A = ((r : ℂ) : ExtPlane)) : A ≠ 1 ∧ A ≠ -1 := by
  constructor
  · intro he
    rw [he] at h
    simp [repellingFixedPoint] at h
  · intro he
    rw [he] at h
    simp [repellingFixedPoint] at h

private theorem compact_cover_trace_ne_zero
    {X : Type*} [TopologicalSpace X] (R : Surfaces.ClosedRiemannSurface X)
    {Γ : Subgroup TraceSL} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {A : TraceSL} (hA : A ∈ Γ) : slTrace A ≠ 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  by_cases hpm : A = 1 ∨ A = -1
  · have ht := s27f_tr_pm_one hpm
    change |slTrace A| = 2 at ht
    intro hzero
    rw [hzero, abs_zero] at ht
    norm_num at ht
  · push Not at hpm
    have ht := s27f_hyp hp hA hpm.1 hpm.2
    change 2 < |slTrace A| at ht
    intro hzero
    rw [hzero, abs_zero] at ht
    linarith

/-- Every transformation in the actual finite normalized system is determined
by exactly the original finite absolute-trace observations, up to the harmless
sign of its determinant-one representative. The lists need only lie in the
original groups; the stronger fact that they generate is not needed. -/
theorem original_closed_uniformization_finite_traces_determine
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (R : Surfaces.ClosedRiemannSurface X) (R' : Surfaces.ClosedRiemannSurface Y)
    {Γ Γ' : Subgroup TraceSL} (p : ℍ → X) (p' : ℍ → Y)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (hp' : let := R'.toRiemannAtlas.toChartedSpace; IsUniformization Γ' p')
    {m : ℕ} (γ δ : Fin (m + 2) → TraceSL)
    (hγ : ∀ j, γ j ∈ Γ) (hδ : ∀ j, δ j ∈ Γ')
    (hnγ : FixedPointNormalizedPair γ) (hnδ : FixedPointNormalizedPair δ)
    (htr : SameBookTraceData γ δ) : ∀ j, δ j = γ j ∨ δ j = -(γ j) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R'.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let := R'.compactSpace
  rcases hnγ with ⟨haγ, hrγ, r, hr, hbγ, hsγ⟩
  rcases hnδ with ⟨haδ, hrδ, r', hr', hbδ, hsδ⟩
  have hcγ := noncentral_of_finite_repelling hrγ
  have hcδ := noncentral_of_finite_repelling hrδ
  have hcγ1 := noncentral_of_finite_repelling hsγ
  have hcδ1 := noncentral_of_finite_repelling hsδ
  obtain ⟨A, hAg, hA⟩ := exists_positive_diagonal_of_fixedpoints (γ 0)
    (s27f_hyp hp (hγ 0) hcγ.1 hcγ.2) haγ hrγ
  obtain ⟨A', hAd, hA'⟩ := exists_positive_diagonal_of_fixedpoints (δ 0)
    (s27f_hyp hp' (hδ 0) hcδ.1 hcδ.2) haδ hrδ
  obtain ⟨B, hBg, hB⟩ := exists_positive_matrix_of_fixedpoints (γ 1)
    (s27f_hyp hp (hγ 1) hcγ1.1 hcγ1.2) hr hbγ hsγ
  obtain ⟨B', hBd, hB'⟩ := exists_positive_matrix_of_fixedpoints (δ 1)
    (s27f_hyp hp' (hδ 1) hcδ1.1 hcδ1.2) hr' hbδ hsδ
  exact finite_book_traces_separate_positive_representatives htr
    (fun j => compact_cover_trace_ne_zero R p hp (hγ j))
    A B A' B' hAg hBg hAd hBd hA hA' hB hB'

/-- The result concerns the original Möbius transformations themselves;
their actions agree at every point of the actual upper half-plane. -/
theorem original_closed_uniformization_finite_traces_same_action
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (R : Surfaces.ClosedRiemannSurface X) (R' : Surfaces.ClosedRiemannSurface Y)
    {Γ Γ' : Subgroup TraceSL} (p : ℍ → X) (p' : ℍ → Y)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (hp' : let := R'.toRiemannAtlas.toChartedSpace; IsUniformization Γ' p')
    {m : ℕ} (γ δ : Fin (m + 2) → TraceSL)
    (hγ : ∀ j, γ j ∈ Γ) (hδ : ∀ j, δ j ∈ Γ')
    (hnγ : FixedPointNormalizedPair γ) (hnδ : FixedPointNormalizedPair δ)
    (htr : SameBookTraceData γ δ) : ∀ j (z : ℍ), δ j • z = γ j • z := by
  intro j z
  rcases original_closed_uniformization_finite_traces_determine R R' p p' hp hp'
    γ δ hγ hδ hnγ hnδ htr j with h | h
  · rw [h]
  · rw [h]
    exact s30l_neg_smul _ _

end LowDimensionalTopology.Geometry.Teichmuller
