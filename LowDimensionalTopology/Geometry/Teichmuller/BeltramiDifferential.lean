module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous Beltrami differentials in a given complex atlas

A differential is a family of continuous chart coefficients satisfying the
actual (-1,1) change-of-coordinate law. It is not a scalar-valued function on
the surface. The norm of its coefficients does descend to a continuous real
function. This file does not identify a norm unit ball with coefficients
realized by diffeomorphisms.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

variable {X : Type u} [TopologicalSpace X]

namespace BeltramiDifferential

/-- An actual member of the specified original atlas. -/
abbrev Chart (A : RiemannAtlas X) :=
  {e : OpenPartialHomeomorph X ℂ // e ∈ A.charts}

/-- A family of continuous complex coefficients on actual chart targets. -/
abbrev Coefficients (A : RiemannAtlas X) :=
  ∀ e : Chart A, C(e.val.target, ℂ)

/-- The concrete (-1,1) transformation law on every actual chart overlap. -/
def Compatible (A : RiemannAtlas X) (μ : Coefficients A) : Prop :=
  ∀ (e f : Chart A) (x : X) (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source),
    μ e ⟨e.val x, e.val.map_source hxe⟩ =
      μ f ⟨f.val x, f.val.map_source hxf⟩ *
        conj (deriv (e.val.symm.trans f.val) (e.val x)) /
          deriv (e.val.symm.trans f.val) (e.val x)

/-- The coordinate law is complex linear in the coefficient family. -/
def coefficientSubmodule (A : RiemannAtlas X) : Submodule ℂ (Coefficients A) where
  carrier := Compatible A
  zero_mem' := by
    intro e f x hxe hxf
    simp
  add_mem' := by
    intro μ ν hμ hν e f x hxe hxf
    change μ e ⟨e.val x, e.val.map_source hxe⟩ +
        ν e ⟨e.val x, e.val.map_source hxe⟩ =
      (μ f ⟨f.val x, f.val.map_source hxf⟩ +
          ν f ⟨f.val x, f.val.map_source hxf⟩) *
        conj (deriv (e.val.symm.trans f.val) (e.val x)) /
          deriv (e.val.symm.trans f.val) (e.val x)
    rw [hμ e f x hxe hxf, hν e f x hxe hxf]
    ring
  smul_mem' := by
    intro a μ hμ e f x hxe hxf
    change a * μ e ⟨e.val x, e.val.map_source hxe⟩ =
      (a * μ f ⟨f.val x, f.val.map_source hxf⟩) *
        conj (deriv (e.val.symm.trans f.val) (e.val x)) /
          deriv (e.val.symm.trans f.val) (e.val x)
    rw [hμ e f x hxe hxf]
    ring

end BeltramiDifferential

/-- A continuous (-1,1) differential, with its concrete original-atlas compatibility.
The complex vector-space operations are inherited from a genuine submodule. -/
abbrev BeltramiDifferential (A : RiemannAtlas X) :=
  ↥(BeltramiDifferential.coefficientSubmodule A)

namespace BeltramiDifferential

variable {A : RiemannAtlas X}

/-- The actual continuous coefficient in a specified chart. -/
def coeff (μ : BeltramiDifferential A) (e : Chart A) : C(e.val.target, ℂ) :=
  μ.val e

@[ext]
theorem ext {μ ν : BeltramiDifferential A}
    (h : ∀ (e : Chart A) (z : e.val.target), μ.coeff e z = ν.coeff e z) : μ = ν := by
  apply Subtype.ext
  funext e
  exact ContinuousMap.ext (h e)

@[simp]
theorem coeff_zero (e : Chart A) (z : e.val.target) :
    (0 : BeltramiDifferential A).coeff e z = 0 := rfl

@[simp]
theorem coeff_add (μ ν : BeltramiDifferential A) (e : Chart A) (z : e.val.target) :
    (μ + ν).coeff e z = μ.coeff e z + ν.coeff e z := rfl

@[simp]
theorem coeff_neg (μ : BeltramiDifferential A) (e : Chart A) (z : e.val.target) :
    (-μ).coeff e z = -μ.coeff e z := rfl

@[simp]
theorem coeff_sub (μ ν : BeltramiDifferential A) (e : Chart A) (z : e.val.target) :
    (μ - ν).coeff e z = μ.coeff e z - ν.coeff e z := rfl

@[simp]
theorem coeff_smul (a : ℂ) (μ : BeltramiDifferential A)
    (e : Chart A) (z : e.val.target) :
    (a • μ).coeff e z = a * μ.coeff e z := rfl

/-- The defining law at a surface point lying in both charts. -/
theorem compatible (μ : BeltramiDifferential A) (e f : Chart A)
    (x : X) (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) :
    μ.coeff e ⟨e.val x, e.val.map_source hxe⟩ =
      μ.coeff f ⟨f.val x, f.val.map_source hxf⟩ *
        conj (deriv (e.val.symm.trans f.val) (e.val x)) /
          deriv (e.val.symm.trans f.val) (e.val x) :=
  μ.property e f x hxe hxf

/-- The same law in the original transition-map coordinates, on its actual source. -/
theorem transition_law (μ : BeltramiDifferential A) (e f : Chart A)
    (z : ℂ) (hz : z ∈ (e.val.symm.trans f.val).source) :
    μ.coeff e ⟨z, hz.1⟩ =
      μ.coeff f ⟨(e.val.symm.trans f.val) z,
        ((e.val.symm.trans f.val).map_source hz).1⟩ *
        conj (deriv (e.val.symm.trans f.val) z) /
          deriv (e.val.symm.trans f.val) z := by
  have hxe : e.val.symm z ∈ e.val.source := e.val.map_target hz.1
  have hxf : e.val.symm z ∈ f.val.source := hz.2
  have h := μ.compatible e f (e.val.symm z) hxe hxf
  simpa only [e.val.right_inv hz.1, OpenPartialHomeomorph.trans_apply] using h

/-- The complex transition derivative is nonzero because of the original analytic atlas. -/
theorem transition_deriv_ne_zero (e f : Chart A)
    (x : X) (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) :
    deriv (e.val.symm.trans f.val) (e.val x) ≠ 0 := by
  apply A.transition_deriv_ne_zero e.val f.val e.property f.property
  refine ⟨e.val.map_source hxe, ?_⟩
  change e.val.symm (e.val x) ∈ f.val.source
  rwa [e.val.left_inv hxe]

/-- The absolute value of a coefficient is independent of the chosen chart. -/
theorem norm_coeff_eq (μ : BeltramiDifferential A) (e f : Chart A)
    (x : X) (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) :
    ‖μ.coeff e ⟨e.val x, e.val.map_source hxe⟩‖ =
      ‖μ.coeff f ⟨f.val x, f.val.map_source hxf⟩‖ := by
  have hd := transition_deriv_ne_zero e f x hxe hxf
  have hnorm : ‖deriv (e.val.symm.trans f.val) (e.val x)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hd
  have h := congrArg (fun w : ℂ => ‖w‖) (μ.compatible e f x hxe hxf)
  rw [norm_div, norm_mul, Complex.norm_conj, mul_div_cancel_right₀ _ hnorm] at h
  exact h

/-- Select an original chart only to define the globally intrinsic pointwise norm. -/
def pointwiseNorm (μ : BeltramiDifferential A) (x : X) : ℝ :=
  ‖μ.coeff ⟨(A.cover x).choose, (A.cover x).choose_spec.1⟩
    ⟨(A.cover x).choose x,
      (A.cover x).choose.map_source (A.cover x).choose_spec.2⟩‖

/-- Every original chart computes the same chosen pointwise norm. -/
theorem pointwiseNorm_eq_coeff (μ : BeltramiDifferential A) (e : Chart A)
    (x : X) (hx : x ∈ e.val.source) :
    μ.pointwiseNorm x = ‖μ.coeff e ⟨e.val x, e.val.map_source hx⟩‖ :=
  μ.norm_coeff_eq ⟨(A.cover x).choose, (A.cover x).choose_spec.1⟩
    e x (A.cover x).choose_spec.2 hx

theorem pointwiseNorm_nonneg (μ : BeltramiDifferential A) (x : X) :
    0 ≤ μ.pointwiseNorm x := norm_nonneg _

/-- The intrinsic coefficient norm is continuous in the original surface topology. -/
theorem continuous_pointwiseNorm (μ : BeltramiDifferential A) :
    Continuous μ.pointwiseNorm := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, he, hx⟩ := A.cover x
  let E : Chart A := ⟨e, he⟩
  have hchart : Continuous (fun y : e.source =>
      (⟨e y.val, e.map_source y.property⟩ : e.target)) :=
    e.continuousOn.mapsToRestrict (fun y hy => e.map_source hy)
  have hlocal : Continuous (fun y : e.source =>
      ‖μ.coeff E ⟨e y.val, e.map_source y.property⟩‖) :=
    (μ.coeff E).continuous.norm.comp hchart
  have hrestriction : Continuous (fun y : e.source => μ.pointwiseNorm y.val) :=
    hlocal.congr (fun y => (μ.pointwiseNorm_eq_coeff E y.val y.property).symm)
  have hOn : ContinuousOn μ.pointwiseNorm e.source :=
    continuousOn_iff_continuous_domRestrict.mpr hrestriction
  exact hOn.continuousAt (e.open_source.mem_nhds hx)

/-- The tensor has an intrinsic continuous absolute-value function, despite not being
itself a scalar-valued surface function. -/
def abs (μ : BeltramiDifferential A) : C(X, ℝ) :=
  ⟨μ.pointwiseNorm, μ.continuous_pointwiseNorm⟩

theorem abs_eq_coeff (μ : BeltramiDifferential A) (e : Chart A)
    (x : X) (hx : x ∈ e.val.source) :
    μ.abs x = ‖μ.coeff e ⟨e.val x, e.val.map_source hx⟩‖ :=
  μ.pointwiseNorm_eq_coeff e x hx

theorem abs_nonneg (μ : BeltramiDifferential A) (x : X) : 0 ≤ μ.abs x :=
  μ.pointwiseNorm_nonneg x

@[simp]
theorem abs_zero (x : X) : (0 : BeltramiDifferential A).abs x = 0 := by
  obtain ⟨e, he, hx⟩ := A.cover x
  rw [abs_eq_coeff _ ⟨e, he⟩ x hx]
  change ‖(0 : ℂ)‖ = 0
  exact norm_zero

theorem abs_add_le (μ ν : BeltramiDifferential A) (x : X) :
    (μ + ν).abs x ≤ μ.abs x + ν.abs x := by
  obtain ⟨e, he, hx⟩ := A.cover x
  rw [abs_eq_coeff _ ⟨e, he⟩ x hx, abs_eq_coeff μ ⟨e, he⟩ x hx,
    abs_eq_coeff ν ⟨e, he⟩ x hx, coeff_add]
  exact norm_add_le _ _

@[simp]
theorem abs_smul (a : ℂ) (μ : BeltramiDifferential A) (x : X) :
    (a • μ).abs x = ‖a‖ * μ.abs x := by
  obtain ⟨e, he, hx⟩ := A.cover x
  rw [abs_eq_coeff _ ⟨e, he⟩ x hx, abs_eq_coeff μ ⟨e, he⟩ x hx,
    coeff_smul, norm_mul]

section Compact

variable [CompactSpace X]

/-- A finite supremum norm obtained from the actual continuous absolute value. -/
def supNorm (μ : BeltramiDifferential A) : ℝ := ‖μ.abs‖

theorem supNorm_nonneg (μ : BeltramiDifferential A) : 0 ≤ μ.supNorm :=
  norm_nonneg _

/-- Every coefficient is bounded by the intrinsic compact-surface supremum norm. -/
theorem abs_le_supNorm (μ : BeltramiDifferential A) (x : X) :
    μ.abs x ≤ μ.supNorm := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (μ.abs_nonneg x), supNorm] using
    μ.abs.norm_coe_le_norm x

theorem coeff_norm_le_supNorm (μ : BeltramiDifferential A) (e : Chart A)
    (z : e.val.target) : ‖μ.coeff e z‖ ≤ μ.supNorm := by
  have hx : e.val.symm z.val ∈ e.val.source := e.val.map_target z.property
  have h := μ.abs_le_supNorm (e.val.symm z.val)
  rw [μ.abs_eq_coeff e (e.val.symm z.val) hx] at h
  simpa only [e.val.right_inv z.property] using h

/-- Compactness gives one bound for all actual-chart coefficient functions. -/
theorem coefficients_bounded (μ : BeltramiDifferential A) :
    ∃ M : ℝ, ∀ (e : Chart A) (z : e.val.target), ‖μ.coeff e z‖ ≤ M :=
  ⟨μ.supNorm, μ.coeff_norm_le_supNorm⟩

end Compact

end BeltramiDifferential

end LowDimensionalTopology.Geometry.Teichmuller
