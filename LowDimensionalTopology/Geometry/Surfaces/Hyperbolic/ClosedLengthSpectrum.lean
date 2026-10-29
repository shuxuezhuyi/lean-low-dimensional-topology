module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import Mathlib.Topology.DiscreteSubset

/-!
# Finite bounded free-loop classes and squared traces

All loops belong to the original surface. Their length is the actual infimum of
Poincaré integrals of Lipschitz lifts in the actual free homotopy class. No
primitive-loop restriction or enumeration is imposed. Finite bounded free
classes retain multiplicity before passing to the set of positive lengths.

The analytic covering and conjugacy arguments use Wu Xiaobin's
Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0), in particular
`Ch08/S30_ModularGroupDiscontinuity.lean`. The bounded-class proof adapts its
`thm30_1_discrete` argument to the actual quotient of ALL free loop classes.
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- Free homotopy of actual original-surface loops, allowing the base point to move. -/
def freeLoopSetoid (X : Type u) [TopologicalSpace X] : Setoid (LiZhongQC.Loop X) where
  r := LiZhongQC.FreelyHomotopic
  iseqv := ⟨fun _ => LiZhongQC.s30b_fh_of_eq (fun _ => rfl),
    fun h => LiZhongQC.s30b_fh_symm h, fun h k => LiZhongQC.s30b_fh_trans h k⟩

/-- All free homotopy classes of continuous loops on the original carrier. -/
abbrev FreeLoopClass (X : Type u) [TopologicalSpace X] := Quotient (freeLoopSetoid X)

/-- The actual Poincaré infimum in a free loop class for a specified plane cover. -/
def freeLoopClassLength {X : Type u} [TopologicalSpace X] (p : ℍ → X) :
    FreeLoopClass X → ℝ≥0∞ :=
  Quotient.lift (LiZhongQC.freeHomotopyLength p)
    (fun _ _ h => LiZhongQC.s30b_fhl_congr p h)

@[simp]
theorem freeLoopClassLength_mk {X : Type u} [TopologicalSpace X]
    (p : ℍ → X) (α : LiZhongQC.Loop X) :
    freeLoopClassLength p (Quotient.mk (freeLoopSetoid X) α) =
      LiZhongQC.freeHomotopyLength p α := rfl

theorem freeLoopClassLength_out {X : Type u} [TopologicalSpace X]
    (p : ℍ → X) (c : FreeLoopClass X) :
    freeLoopClassLength p c = LiZhongQC.freeHomotopyLength p (Quotient.out c) := by
  exact (congrArg (freeLoopClassLength p) (Quotient.out_eq' c)).symm

/-- Positive lengths represented by all original free loop classes. -/
def positiveFreeLengthSpectrum {X : Type u} [TopologicalSpace X] (p : ℍ → X) : Set ℝ :=
  {ℓ | 0 < ℓ ∧ ∃ c : FreeLoopClass X, freeLoopClassLength p c = ENNReal.ofReal ℓ}

private theorem closed_discrete_of_finite_le (s : Set ℝ)
    (hs : ∀ L : ℝ, {x ∈ s | x ≤ L}.Finite) : IsClosed s ∧ DiscreteTopology ↥s := by
  have h : IsClosed s ∧ IsDiscrete s := isClosed_and_discrete_iff.mpr (by
    intro x
    rw [disjoint_principal_right]
    let F : Set ℝ := {y ∈ s | y ≤ x + 1}
    have hF : F.Finite := hs (x + 1)
    have hFc : IsClosed (F \ {x}) := hF.sdiff.isClosed
    have hav : (F \ {x})ᶜ ∈ 𝓝 x :=
      hFc.isOpen_compl.mem_nhds (by simp)
    have hup : Iio (x + 1) ∈ 𝓝 x := Iio_mem_nhds (by linarith)
    have hav' : (F \ {x})ᶜ ∈ 𝓝[≠] x := nhdsWithin_le_nhds hav
    have hup' : Iio (x + 1) ∈ 𝓝[≠] x := nhdsWithin_le_nhds hup
    filter_upwards [hav', hup', self_mem_nhdsWithin] with y hy hyup hyne
    intro hys
    exact hy ⟨⟨hys, hyup.le⟩, hyne⟩)
  exact ⟨h.1, h.2.to_subtype⟩

namespace ClosedRiemannSurface

/-- Only finitely many actual free homotopy classes have bounded Poincaré length.
The cover is an actual holomorphic uniformization of the original complex atlas. -/
theorem bounded_freeLoopClasses_finite
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (M : ℝ) : {c : FreeLoopClass X | freeLoopClassLength p c ≤ ENNReal.ofReal M}.Finite := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.compactSpace
  have hF : LiZhongQC.IsFuchsian Γ := LiZhongQC.utm_x2_isFuchsian hp
  have hfree := LiZhongQC.s27g_actsFreely hp
  have hC := LiZhongQC.utm_exists_compact_translate hp
  let α : FreeLoopClass X → LiZhongQC.Loop X := Quotient.out
  have hinj (a b : FreeLoopClass X)
      (hab : LiZhongQC.FreelyHomotopic (α a) (α b)) : a = b := by
    calc
      a = Quotient.mk (freeLoopSetoid X) (α a) := (Quotient.out_eq' a).symm
      _ = Quotient.mk (freeLoopSetoid X) (α b) := Quotient.sound hab
      _ = b := Quotient.out_eq' b
  choose γs hγs hcovs using fun c => LiZhongQC.s30a_exists_covers hp (α c)
  obtain ⟨_, F, hFprop⟩ := LiZhongQC.lengthSpectrum_discrete hF hfree hC M
  let S₀ : Set (FreeLoopClass X) := {c | γs c = 1 ∨ γs c = -1}
  let Sc : Matrix.SpecialLinearGroup (Fin 2) ℝ → Set (FreeLoopClass X) :=
    fun γ' => {c | ∃ δ ∈ Γ, γs c = δ * γ' * δ⁻¹}
  have hpm : ∀ c ∈ S₀, ∀ x : ℍ, γs c • x = x := by
    rintro c (h | h) x
    · rw [h, one_smul]
    · rw [h, LiZhongQC.s27g_neg_one_smul]
  have hS₀ : S₀.Subsingleton := by
    intro c hc d hd
    refine hinj c d (LiZhongQC.s30a_fh_of_conj hp (hγs c) Γ.one_mem
      (fun x => ?_) (hcovs c) (hcovs d))
    rw [hpm d hd, inv_one, mul_one, one_mul, hpm c hc]
  have hSc : ∀ γ', (Sc γ').Subsingleton := by
    rintro γ' c ⟨δ, hδ, hc⟩ d ⟨δ', hδ', hd⟩
    refine hinj c d (LiZhongQC.s30a_fh_of_conj hp (hγs c)
      (Γ.mul_mem hδ' (Γ.inv_mem hδ)) (fun x => ?_) (hcovs c) (hcovs d))
    rw [hd, hc]
    congr 1
    group
  refine ((hS₀.finite.union (F.finite_toSet.biUnion fun γ' _ => (hSc γ').finite))).subset ?_
  intro c hc
  by_cases h01 : γs c = 1 ∨ γs c = -1
  · exact Or.inl h01
  push Not at h01
  have hh : LiZhongQC.IsHyperbolic (γs c) :=
    LiZhongQC.s27f_hyp hp (hγs c) h01.1 h01.2
  have hlen := LiZhongQC.s30a_len_hyp hp (hγs c) hh (hcovs c)
  have hle : LiZhongQC.freeHomotopyLength p (α c) ≤ ENNReal.ofReal M := by
    exact (freeLoopClassLength_out p c) ▸ hc
  rw [hlen] at hle
  have htl : LiZhongQC.translationLength (γs c) ≤ M := by
    rcases ENNReal.ofReal_le_ofReal_iff'.1 hle with h | h
    · exact h
    · exact absurd h (not_le.2 (LiZhongQC.s30a_tl_pos hh))
  obtain ⟨δ, hδ, γ', hγ', heq⟩ := hFprop (γs c) (hγs c) hh htl
  exact Or.inr (Set.mem_biUnion hγ' ⟨δ, hδ, heq⟩)

/-- Multiplicity is controlled at the level of ALL free loop classes, before
forgetting the class and retaining only its numerical length. -/
theorem freeLoopClasses_of_length_finite
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ℓ : ℝ) : {c : FreeLoopClass X | freeLoopClassLength p c = ENNReal.ofReal ℓ}.Finite :=
  (R.bounded_freeLoopClasses_finite p hp ℓ).subset fun _ h => h.le

/-- Every bounded part of the positive length-value set is finite. -/
theorem positiveFreeLengthSpectrum_finite_le
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (M : ℝ) : {ℓ ∈ positiveFreeLengthSpectrum p | ℓ ≤ M}.Finite := by
  classical
  refine ((R.bounded_freeLoopClasses_finite p hp M).image
    (fun c => (freeLoopClassLength p c).toReal)).subset ?_
  rintro ℓ ⟨⟨hℓ, c, hc⟩, hM⟩
  refine ⟨c, ?_, ?_⟩
  · exact hc.le.trans (ENNReal.ofReal_le_ofReal hM)
  · simp only [hc, ENNReal.toReal_ofReal hℓ.le]

/-- The positive length values form a closed discrete real set. -/
theorem positiveFreeLengthSpectrum_closed_discrete
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    IsClosed (positiveFreeLengthSpectrum p) ∧ DiscreteTopology ↥(positiveFreeLengthSpectrum p) :=
  closed_discrete_of_finite_le _ (R.positiveFreeLengthSpectrum_finite_le p hp)

end ClosedRiemannSurface
end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The actual squared traces of all matrices of the original Fuchsian group. -/
def squaredTraceSpectrum (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ℝ :=
  {t | ∃ γ ∈ Γ, t = (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2}

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u

/-- A bounded squared trace gives an explicitly bounded hyperbolic translation
length. The underlying original matrix is retained. -/
private theorem translationLength_le_of_sqtrace_le
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hh : LiZhongQC.IsHyperbolic γ)
    (B : ℝ) (hB : LiZhongQC.slTrace γ ^ 2 ≤ B) :
    LiZhongQC.translationLength γ ≤ 2 * Real.arsinh (Real.sqrt (max B 0) / 2) := by
  have h4 : 0 ≤ LiZhongQC.slTrace γ ^ 2 - 4 := by
    have h2 : 2 < |LiZhongQC.slTrace γ| := hh
    nlinarith [sq_abs (LiZhongQC.slTrace γ), abs_nonneg (LiZhongQC.slTrace γ)]
  rw [LiZhongQC.translationLength_eq_arsinh h4]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.arsinh_le_arsinh.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Real.sqrt_le_sqrt (by linarith [le_max_left B 0])

/-- Each bounded part of the squared-trace set is finite, including trace square
4 of the identity sign representatives. No primitive-element restriction is used. -/
theorem squaredTraceSpectrum_finite_le
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (B : ℝ) : {t ∈ Fuchsian.squaredTraceSpectrum Γ | t ≤ B}.Finite := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.compactSpace
  have hF := LiZhongQC.utm_x2_isFuchsian hp
  have hfree := LiZhongQC.s27g_actsFreely hp
  have hC := LiZhongQC.utm_exists_compact_translate hp
  obtain ⟨_, F, hFprop⟩ := LiZhongQC.lengthSpectrum_discrete hF hfree hC
    (2 * Real.arsinh (Real.sqrt (max B 0) / 2))
  refine ((Set.finite_singleton (4 : ℝ)).union
    (F.finite_toSet.image (fun γ => LiZhongQC.slTrace γ ^ 2))).subset ?_
  rintro t ⟨⟨γ, hγ, rfl⟩, ht⟩
  have htrace : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ) = LiZhongQC.slTrace γ := by
    simp only [Matrix.trace_fin_two, LiZhongQC.slTrace]
  rw [htrace] at ht ⊢
  by_cases h1 : γ = 1
  · left
    norm_num [h1, LiZhongQC.slTrace]
  by_cases h2 : γ = -1
  · left
    norm_num [h2, LiZhongQC.slTrace]
  have hh : LiZhongQC.IsHyperbolic γ := LiZhongQC.s27f_hyp hp hγ h1 h2
  have htl := translationLength_le_of_sqtrace_le γ hh B ht
  obtain ⟨δ, hδ, γ', hγ', hconj⟩ := hFprop γ hγ hh htl
  right
  refine ⟨γ', hγ', ?_⟩
  rw [hconj, LiZhongQC.slTrace_conj]

/-- All actual squared traces form a closed discrete subset of the real line. -/
theorem squaredTraceSpectrum_closed_discrete
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    IsClosed (Fuchsian.squaredTraceSpectrum Γ) ∧ DiscreteTopology ↥(Fuchsian.squaredTraceSpectrum Γ) :=
  closed_discrete_of_finite_le _ (R.squaredTraceSpectrum_finite_le p hp)

/-- Every original closed surface of native handle genus greater than one has an
actual original-atlas hyperbolic cover with the finite-class and discrete-spectrum
properties. A covering model is constructed, rather than assumed as extra input. -/
theorem exists_uniformization_discrete_spectra
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : ℍ → X),
      LiZhongQC.IsUniformization Γ p ∧
      (∀ M : ℝ, {c : FreeLoopClass X | freeLoopClassLength p c ≤ ENNReal.ofReal M}.Finite) ∧
      IsClosed (positiveFreeLengthSpectrum p) ∧ DiscreteTopology ↥(positiveFreeLengthSpectrum p) ∧
      IsClosed (Fuchsian.squaredTraceSpectrum Γ) ∧ DiscreteTopology ↥(Fuchsian.squaredTraceSpectrum Γ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  have hR := R.hasSourceGenus hgenus
  obtain ⟨Γ, p, _, _, hp⟩ := LiZhongQC.s22hg_exists_fuchsian_uniformization hg hR
  obtain ⟨hlc, hld⟩ := R.positiveFreeLengthSpectrum_closed_discrete p hp
  obtain ⟨htc, htd⟩ := R.squaredTraceSpectrum_closed_discrete p hp
  exact ⟨Γ, p, hp, R.bounded_freeLoopClasses_finite p hp, hlc, hld, htc, htd⟩

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface
