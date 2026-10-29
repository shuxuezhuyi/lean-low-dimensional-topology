module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ClosedLengthSpectrum
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# The full original closed-geodesic spectrum and finite multiplicity

The actual original-atlas BV length of every arbitrary-parameter periodic
geodesic equals the free-class length. Its geometric image together with
its full-period length is independent of the original parametrization.
Keeping that pair retains proper-power multiplicity: the same geometric
image with different full traversals has different length data.

Finite bounded free classes therefore give finite bounded original
geodesic data, and the numerical length spectrum is a closed discrete set.
All free classes, curves, surfaces, coverings and length normalizations are
unchanged. The original genus hypothesis constructs the hyperbolic model.
The credited source covering and length theorems reuse Li-Zhong-QC at
commit `1c0d5473c020b66ed5106331a38a61536760b9b2`; see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Hyperbolic

/-- The full actual original BV geodesic length is the original free-class
infimum, with the complete covering matrix and proper powers retained. -/
theorem OriginalClosedGeodesic.length_eq_freeHomotopyLength
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    q.length = LiZhongQC.freeHomotopyLength M.halfPlaneCover q.toLoop := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hdeck, hcov, _, ht, hlen, _⟩ := q.exists_actual_matrix_length_trace
  have hh : LiZhongQC.IsHyperbolic A := by
    unfold LiZhongQC.IsHyperbolic LiZhongQC.slTrace
    change 2 < |A.val 0 0 + A.val 1 1|
    rw [← Matrix.trace_fin_two]
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  have hfree := LiZhongQC.s30a_len_hyp hp ((hΓ A).2 hdeck) hh hcov
  exact hlen.trans ((congrArg ENNReal.ofReal
    (liZhong_translationLength_eq_native A hh)).symm.trans hfree.symm)

/-- Every actual original closed geodesic has positive finite full-period length. -/
theorem OriginalClosedGeodesic.length_pos_and_ne_top
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    0 < q.length ∧ q.length ≠ ⊤ := by
  obtain ⟨A, _, _, hA, ht, hlen, _⟩ := q.exists_actual_matrix_length_trace
  rw [hlen]
  exact ⟨ENNReal.ofReal_pos.mpr (hHyperbolic_translationLength_pos A hA ht),
    ENNReal.ofReal_ne_top⟩

/-- An actual locally minimizing closed geodesic cannot be freely null-homotopic. -/
theorem OriginalClosedGeodesic.not_isNullHomotopicLoop
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    ¬ IsNullHomotopicLoop q.toLoop := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  rintro ⟨x, hx⟩
  obtain ⟨τ, hτ⟩ := M.halfPlaneCover_surjective x
  have hcov : LiZhongQC.Covers M.halfPlaneCover 1 (constantLoop x) := by
    refine ⟨fun _ => τ, continuous_const.continuousOn, ?_, ?_⟩
    · intro t _
      simpa only [constantLoop, Path.refl_extend, ContinuousMap.const_apply] using hτ
    · exact (one_smul _ _).symm
  have hzero := LiZhongQC.s30a_len_zero hp Γ.one_mem (Or.inl rfl) hcov
  have hlength : q.length = 0 := q.length_eq_freeHomotopyLength.trans
    ((LiZhongQC.s30b_fhl_congr M.halfPlaneCover hx).trans hzero)
  exact (ne_of_gt q.length_pos_and_ne_top.1) hlength

/-- Unparametrized original geodesic data retain the complete traversal length. -/
def OriginalClosedGeodesic.lengthTrace
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) : Set X × ℝ≥0∞ :=
  (range q.curve, q.length)

/-- The same actual free class has one geometric image and one full-period length. -/
theorem OriginalClosedGeodesic.lengthTrace_eq_of_freelyHomotopic
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    (h : LiZhongQC.FreelyHomotopic q.toLoop r.toLoop) : q.lengthTrace = r.lengthTrace := by
  refine Prod.ext (q.trace_eq_of_freelyHomotopic r q.not_isNullHomotopicLoop h) ?_
  exact q.length_eq_freeHomotopyLength.trans
    ((LiZhongQC.s30b_fhl_congr M.halfPlaneCover h).trans r.length_eq_freeHomotopyLength.symm)

/-- Geometric images paired with their full original lengths, including all powers. -/
def originalClosedGeodesicData
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) : Set (Set X × ℝ≥0∞) :=
  range (fun q : OriginalClosedGeodesic M => q.lengthTrace)

/-- The numerical lengths of the actual original closed geodesics. -/
def originalClosedGeodesicLengthSpectrum
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) : Set ℝ :=
  range (fun q : OriginalClosedGeodesic M => q.length.toReal)

namespace ClosedRiemannSurface

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Bounded actual original closed-geodesic data are finite before forgetting
full traversal lengths; no primitive or simple-geodesic restriction is imposed. -/
theorem bounded_originalClosedGeodesicData_finite
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (L : ℝ) :
    {v ∈ originalClosedGeodesicData M | v.2 ≤ ENNReal.ofReal L}.Finite := by
  let := R.compactSpace
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  let B : Set (FreeLoopClass X) :=
    {c | freeLoopClassLength M.halfPlaneCover c ≤ ENNReal.ofReal L}
  have hB : B.Finite := R.bounded_freeLoopClasses_finite M.halfPlaneCover hp L
  let F : FreeLoopClass X → Set (Set X × ℝ≥0∞) := fun c =>
    {v | ∃ q : OriginalClosedGeodesic M,
      Quotient.mk (freeLoopSetoid X) q.toLoop = c ∧ q.lengthTrace = v}
  have hF : ∀ c, (F c).Subsingleton := by
    rintro c v ⟨q, hq, hv⟩ w ⟨r, hr, hw⟩
    have hfree : LiZhongQC.FreelyHomotopic q.toLoop r.toLoop :=
      Quotient.exact (hq.trans hr.symm)
    exact hv.symm.trans ((q.lengthTrace_eq_of_freelyHomotopic r hfree).trans hw)
  refine (hB.biUnion (fun c _ => (hF c).finite)).subset ?_
  rintro v ⟨⟨q, rfl⟩, hq⟩
  change q.length ≤ ENNReal.ofReal L at hq
  have hc : Quotient.mk (freeLoopSetoid X) q.toLoop ∈ B := by
    change LiZhongQC.freeHomotopyLength M.halfPlaneCover q.toLoop ≤ ENNReal.ofReal L
    exact q.length_eq_freeHomotopyLength ▸ hq
  exact Set.mem_biUnion hc ⟨q, rfl, rfl⟩

/-- Every fixed length has finitely many actual oriented free classes of
original closed geodesics, including all proper-power classes. -/
theorem originalClosedGeodesic_freeClasses_of_length_finite
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (ℓ : ℝ) :
    {c : FreeLoopClass X | ∃ q : OriginalClosedGeodesic M,
      Quotient.mk (freeLoopSetoid X) q.toLoop = c ∧ q.length = ENNReal.ofReal ℓ}.Finite := by
  let := R.compactSpace
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  refine (R.freeLoopClasses_of_length_finite M.halfPlaneCover hp ℓ).subset ?_
  rintro c ⟨q, rfl, hq⟩
  change LiZhongQC.freeHomotopyLength M.halfPlaneCover q.toLoop = ENNReal.ofReal ℓ
  exact q.length_eq_freeHomotopyLength.symm.trans hq

/-- For every length, only finitely many original geometric closed geodesics
have that full-period length. Original parametrizations and powers remain admitted. -/
theorem originalClosedGeodesic_images_of_length_finite
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (ℓ : ℝ) :
    {S : Set X | ∃ q : OriginalClosedGeodesic M,
      range q.curve = S ∧ q.length = ENNReal.ofReal ℓ}.Finite := by
  have hdata : {v ∈ originalClosedGeodesicData M | v.2 = ENNReal.ofReal ℓ}.Finite :=
    (R.bounded_originalClosedGeodesicData_finite M ℓ).subset fun _ h => ⟨h.1, h.2.le⟩
  refine (hdata.image Prod.fst).subset ?_
  rintro S ⟨q, hS, hℓ⟩
  exact ⟨q.lengthTrace, ⟨⟨q, rfl⟩, hℓ⟩, hS⟩

/-- The literal length values of ALL actual original closed geodesics form a
closed discrete real set, in the unchanged Poincare length normalization. -/
theorem originalClosedGeodesicLengthSpectrum_closed_discrete
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    IsClosed (originalClosedGeodesicLengthSpectrum M) ∧
      DiscreteTopology ↥(originalClosedGeodesicLengthSpectrum M) := by
  let := R.compactSpace
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hsub : originalClosedGeodesicLengthSpectrum M ⊆
      positiveFreeLengthSpectrum M.halfPlaneCover := by
    rintro ℓ ⟨q, rfl⟩
    have hq := q.length_pos_and_ne_top
    refine ⟨ENNReal.toReal_pos hq.1.ne' hq.2,
      Quotient.mk (freeLoopSetoid X) q.toLoop, ?_⟩
    change LiZhongQC.freeHomotopyLength M.halfPlaneCover q.toLoop =
      ENNReal.ofReal q.length.toReal
    exact q.length_eq_freeHomotopyLength.symm.trans (ENNReal.ofReal_toReal hq.2).symm
  obtain ⟨hc, hd⟩ := R.positiveFreeLengthSpectrum_closed_discrete M.halfPlaneCover hp
  exact ⟨isClosed_of_subset_discrete_closed hsub ⟨hd⟩ hc,
    DiscreteTopology.of_subset hd hsub⟩

/-- The original closed genus-at-least-two surface itself supplies its genuine
hyperbolic model, complete discrete geodesic spectrum and finite multiplicities. -/
theorem exists_originalClosedGeodesic_discrete_spectrum
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g) :
    ∃ M : HyperbolicSurfaceModel R.toRiemannSurface,
      IsClosed (originalClosedGeodesicLengthSpectrum M) ∧
      DiscreteTopology ↥(originalClosedGeodesicLengthSpectrum M) ∧
      (∀ L : ℝ, {v ∈ originalClosedGeodesicData M | v.2 ≤ ENNReal.ofReal L}.Finite) ∧
      (∀ ℓ : ℝ, {c : FreeLoopClass X | ∃ q : OriginalClosedGeodesic M,
        Quotient.mk (freeLoopSetoid X) q.toLoop = c ∧ q.length = ENNReal.ofReal ℓ}.Finite) ∧
      (∀ ℓ : ℝ, {S : Set X | ∃ q : OriginalClosedGeodesic M,
        range q.curve = S ∧ q.length = ENNReal.ofReal ℓ}.Finite) := by
  let M : HyperbolicSurfaceModel R.toRiemannSurface :=
    (R.hyperbolicOfGenusGeTwo hg hgenus).model
  obtain ⟨hc, hd⟩ := R.originalClosedGeodesicLengthSpectrum_closed_discrete M
  exact ⟨M, hc, hd, R.bounded_originalClosedGeodesicData_finite M,
    R.originalClosedGeodesic_freeClasses_of_length_finite M,
    R.originalClosedGeodesic_images_of_length_finite M⟩

end ClosedRiemannSurface
end LowDimensionalTopology.Geometry.Surfaces
