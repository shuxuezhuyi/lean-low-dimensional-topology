module

public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami

/-!
# Raw full-atlas families and genuine measurable tensor classes

Every uniformly essentially bounded measurable family satisfying the actual
all-original-chart tensor law encodes into the closed Banach space. Equality of
these genuine classes is exactly coefficientwise almost-everywhere equality,
and every class is recovered from its own chosen representatives.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The genuine coordinate class of an actual measurable coefficient family. -/
def encodeCoordinate {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (e : Chart A) : DomainMeasurableBeltramiSpace e.val.target :=
  (DomainMeasurableBeltramiBall.coefficientMemLp (hq e)).toLp (q e)

theorem encodeCoordinate_coe_ae {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (e : Chart A) : encodeCoordinate q hq e =ᵐ[volume.restrict e.val.target] q e :=
  (DomainMeasurableBeltramiBall.coefficientMemLp (hq e)).coeFn_toLp

theorem norm_encodeCoordinate_le {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (e : Chart A) : ‖encodeCoordinate q hq e‖ ≤ k := by
  apply lpInfinity_norm_le_of_ae_bound _ hk
  filter_upwards [encodeCoordinate_coe_ae q hq e, (hq e).2] with z hz hb
  rw [hz]
  exact hb

/-- A single actual essential bound places the coordinate classes in the genuine bounded product. -/
def encodeAmbient {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k) :
    Ambient A :=
  ⟨fun e => encodeCoordinate q hq e, memℓp_infty ⟨k, by
    rintro _ ⟨e, rfl⟩
    exact norm_encodeCoordinate_le q hk hq e⟩⟩

/-- Encode an actual full-atlas measurable tensor into the closed Banach subspace. -/
def ofFamily {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (hc : ∀ e f : Chart A, ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      q e z = q f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z) : Space A := by
  refine ⟨encodeAmbient q hk hq, (mem_compatibleSubmodule_iff _).2 ?_⟩
  intro e f
  have he := ae_restrict_of_ae_restrict_of_subset
    (fun _ hz => hz.1 : (e.val.symm.trans f.val).source ⊆ e.val.target)
      (encodeCoordinate_coe_ae q hq e)
  have hf := A.transition_ae_pullback e.val f.val e.property f.property
    (encodeCoordinate_coe_ae q hq f)
  filter_upwards [he, hf, hc e f] with z hez hfz hcz
  change encodeCoordinate q hq e z = encodeCoordinate q hq f ((e.val.symm.trans f.val) z) * _
  rw [hez, hfz]
  exact hcz

/-- Encoding retains every original chart coefficient almost everywhere. -/
theorem ofFamily_coe_ae {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (hc : ∀ e f : Chart A, ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      q e z = q f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z) (e : Chart A) :
    coeff (ofFamily q hk hq hc) e =ᵐ[volume.restrict e.val.target] q e :=
  encodeCoordinate_coe_ae q hq e

/-- The intrinsic class norm is bounded by every supplied actual common essential bound. -/
theorem norm_ofFamily_le {A : RiemannAtlas X} (q : Chart A → ℂ → ℂ) {k : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (hc : ∀ e f : Chart A, ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      q e z = q f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z) : ‖ofFamily q hk hq hc‖ ≤ k := by
  apply (norm_le_iff _ hk).2
  intro e
  filter_upwards [ofFamily_coe_ae q hk hq hc e, (hq e).2] with z hz hb
  rw [hz]
  exact hb

/-- Equality is precisely all-original-chart AE equality, independently of bounds and proofs. -/
theorem ofFamily_eq_iff {A : RiemannAtlas X} (q r : Chart A → ℂ → ℂ) {k l : ℝ}
    (hk : 0 ≤ k) (hq : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (q e) e.val.target k)
    (hc : ∀ e f : Chart A, ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      q e z = q f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z)
    (hl : 0 ≤ l) (hr : ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (r e) e.val.target l)
    (hd : ∀ e f : Chart A, ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      r e z = r f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z) :
    ofFamily q hk hq hc = ofFamily r hl hr hd ↔
      ∀ e : Chart A, q e =ᵐ[volume.restrict e.val.target] r e := by
  constructor
  · intro h e
    have he := congrArg (fun μ : Space A => coeff μ e) h
    have hqae := ofFamily_coe_ae q hk hq hc e
    rw [he] at hqae
    exact hqae.symm.trans (ofFamily_coe_ae r hl hr hd e)
  · intro h
    apply Subtype.ext
    apply lp.ext
    funext e
    apply Lp.ext
    exact (ofFamily_coe_ae q hk hq hc e).trans
      ((h e).trans (ofFamily_coe_ae r hl hr hd e).symm)

/-- Every class is recovered from its own actual measurable coefficient representatives. -/
theorem ofFamily_representative {A : RiemannAtlas X} (μ : Space A) :
    ofFamily (fun e => coeff μ e) (norm_nonneg μ)
      (fun e => ⟨Lp.aestronglyMeasurable (coeff μ e),
        (norm_le_iff μ (norm_nonneg μ)).1 le_rfl e⟩)
      (compatible μ) = μ := by
  apply Subtype.ext
  apply lp.ext
  funext e
  apply Lp.ext
  exact ofFamily_coe_ae (fun f => coeff μ f) (norm_nonneg μ)
    (fun f => ⟨Lp.aestronglyMeasurable (coeff μ f),
      (norm_le_iff μ (norm_nonneg μ)).1 le_rfl f⟩) (compatible μ) e

end LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami
