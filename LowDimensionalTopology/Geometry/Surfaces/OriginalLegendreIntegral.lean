module

public import LowDimensionalTopology.Unproved.Surfaces.OriginalLegendreAlgebraicRealization
public import LowDimensionalTopology.External.Jacobians.Monodromy.HolomorphicPrimitives
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Abel

/-!
# The actual Legendre path integral and its periods

The global regular differential is integrated along every actual continuous
path on the same compact cubic. The period subgroup is the range of its
genuine fundamental-group homomorphism. A generating pair gives the integer
span of its two actual integrals, and all path values form the corresponding
period coset.

The primitive path-value APIs are due to Rado Kirov's Jacobians development.
The fundamental-group period construction is reused from the Li Zhong
adaptation maintained in this repository.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped OnePoint Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Choose the specified analytic realization on the same concrete carrier. -/
def originalLegendreRealization
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) : OriginalLegendreRealization l :=
  Classical.choice (hReal l)

/-- The actual primitive integral of the globally regular dz/w form. -/
def legendrePathIntegral {l : LegendreParameter} (D : OriginalLegendreRealization l)
    {a b : LegendreCompactCurve l} (γ : Path a b) : ℂ := by
  letI := D.surface.t2Space
  letI := D.surface.compactSpace
  letI := D.surface.connectedSpace
  letI := D.surface.toRiemannAtlas.toChartedSpace
  letI := D.surface.toRiemannAtlas.isManifold
  exact Jacobians.pathPrimValue D.form γ.extend γ.continuous_extend.continuousOn

/-- Concatenation adds the actual continued elliptic integrals. -/
theorem legendrePathIntegral_concat {l : LegendreParameter}
    (D : OriginalLegendreRealization l) {a b c : LegendreCompactCurve l}
    (p : Path a b) (q : Path b c) :
    legendrePathIntegral D (p.trans q) = legendrePathIntegral D p + legendrePathIntegral D q := by
  let := D.surface.t2Space
  let := D.surface.compactSpace
  let := D.surface.connectedSpace
  let := D.surface.toRiemannAtlas.toChartedSpace
  let := D.surface.toRiemannAtlas.isManifold
  exact LiZhongQC.k22rr_pathPrimValue_concat D.form p q

/-- Endpoint-fixed homotopies preserve the same primitive integral. -/
theorem legendrePathIntegral_homotopic {l : LegendreParameter}
    (D : OriginalLegendreRealization l) {a b : LegendreCompactCurve l}
    {p q : Path a b} (h : p.Homotopic q) :
    legendrePathIntegral D p = legendrePathIntegral D q := by
  let := D.surface.t2Space
  let := D.surface.compactSpace
  let := D.surface.connectedSpace
  let := D.surface.toRiemannAtlas.toChartedSpace
  let := D.surface.toRiemannAtlas.isManifold
  exact Jacobians.pathPrimValue_eq_of_homotopic D.form h

/-- The genuine period homomorphism, together with its exact loop-value law. -/
def legendrePeriodData {l : LegendreParameter} (D : OriginalLegendreRealization l) :
    {P : Additive (FundamentalGroup (LegendreCompactCurve l) ∞) →+ ℂ //
      ∀ γ : Path (∞ : LegendreCompactCurve l) ∞,
        P (Additive.ofMul (FundamentalGroup.fromPath ⟦γ⟧)) = legendrePathIntegral D γ} := by
  letI := D.surface.t2Space
  letI := D.surface.compactSpace
  letI := D.surface.connectedSpace
  letI := D.surface.toRiemannAtlas.toChartedSpace
  letI := D.surface.toRiemannAtlas.isManifold
  let hP := LiZhongQC.k22rr_exists_pi1_period_of_concat D.form (∞ : LegendreCompactCurve l)
    (LiZhongQC.k22rr_pathPrimValue_concat D.form)
  refine ⟨Classical.choose hP, ?_⟩
  intro γ
  exact Classical.choose_spec hP γ

/-- The actual homomorphism of based homotopy classes to elliptic periods. -/
def legendrePeriodHom {l : LegendreParameter} (D : OriginalLegendreRealization l) :
    Additive (FundamentalGroup (LegendreCompactCurve l) ∞) →+ ℂ :=
  (legendrePeriodData D).val

/-- Every original loop evaluates to its own continued dz/w integral. -/
theorem legendrePeriodHom_apply_loop {l : LegendreParameter}
    (D : OriginalLegendreRealization l) (γ : Path (∞ : LegendreCompactCurve l) ∞) :
    legendrePeriodHom D (Additive.ofMul (FundamentalGroup.fromPath ⟦γ⟧)) =
      legendrePathIntegral D γ :=
  (legendrePeriodData D).property γ

/-- All actual periods, retaining every original based loop. -/
def legendrePeriods {l : LegendreParameter} (D : OriginalLegendreRealization l) : AddSubgroup ℂ :=
  (legendrePeriodHom D).range

/-- The original selected-path elliptic integral from the actual point at infinity. -/
def originalEllipticIntegral
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) {p : LegendreCompactCurve l}
    (γ : Path (∞ : LegendreCompactCurve l) p) : ℂ :=
  legendrePathIntegral (originalLegendreRealization hReal l) γ

/-- The period subgroup of that same original elliptic integral. -/
def originalEllipticPeriods
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) : AddSubgroup ℂ :=
  legendrePeriods (originalLegendreRealization hReal l)

/-- Two actual generating loops give precisely the integer span of their integrals. -/
theorem legendrePeriods_eq_two_generator_span {l : LegendreParameter}
    (D : OriginalLegendreRealization l) (a b : Path (∞ : LegendreCompactCurve l) ∞)
    (hgen : Subgroup.closure
      ({FundamentalGroup.fromPath ⟦a⟧, FundamentalGroup.fromPath ⟦b⟧} :
        Set (FundamentalGroup (LegendreCompactCurve l) ∞)) = ⊤) :
    legendrePeriods D = AddSubgroup.zmultiples (legendrePathIntegral D a) ⊔
      AddSubgroup.zmultiples (legendrePathIntegral D b) := by
  let H : AddSubgroup ℂ := AddSubgroup.zmultiples (legendrePathIntegral D a) ⊔
    AddSubgroup.zmultiples (legendrePathIntegral D b)
  have hall : ∀ g : FundamentalGroup (LegendreCompactCurve l) ∞,
      legendrePeriodHom D (Additive.ofMul g) ∈ H := by
    intro g
    have hg : g ∈ Subgroup.closure
        ({FundamentalGroup.fromPath ⟦a⟧, FundamentalGroup.fromPath ⟦b⟧} :
          Set (FundamentalGroup (LegendreCompactCurve l) ∞)) := by
      rw [hgen]
      trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · subst x
        rw [legendrePeriodHom_apply_loop]
        exact (le_sup_left : AddSubgroup.zmultiples (legendrePathIntegral D a) ≤ H)
          (AddSubgroup.mem_zmultiples _)
      · have hx' := Set.mem_singleton_iff.mp hx
        subst x
        rw [legendrePeriodHom_apply_loop]
        exact (le_sup_right : AddSubgroup.zmultiples (legendrePathIntegral D b) ≤ H)
          (AddSubgroup.mem_zmultiples _)
    | one =>
      change legendrePeriodHom D 0 ∈ H
      rw [map_zero]
      exact H.zero_mem
    | mul x y _hx _hy hpx hpy =>
      change legendrePeriodHom D (Additive.ofMul x + Additive.ofMul y) ∈ H
      rw [map_add]
      exact H.add_mem hpx hpy
    | inv x _hx hpx =>
      change legendrePeriodHom D (-Additive.ofMul x) ∈ H
      rw [map_neg]
      exact H.neg_mem hpx
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    exact hall g.toMul
  · refine sup_le ?_ ?_
    · apply AddSubgroup.zmultiples_le.mpr
      exact ⟨Additive.ofMul (FundamentalGroup.fromPath ⟦a⟧), legendrePeriodHom_apply_loop D a⟩
    · apply AddSubgroup.zmultiples_le.mpr
      exact ⟨Additive.ofMul (FundamentalGroup.fromPath ⟦b⟧), legendrePeriodHom_apply_loop D b⟩

/-- The constant loop at infinity has zero integral. -/
theorem legendrePathIntegral_refl_infty {l : LegendreParameter}
    (D : OriginalLegendreRealization l) :
    legendrePathIntegral D (Path.refl (∞ : LegendreCompactCurve l)) = 0 := by
  have h := legendrePeriodHom_apply_loop D (Path.refl (∞ : LegendreCompactCurve l))
  have hclass : Additive.ofMul (FundamentalGroup.fromPath
      ⟦Path.refl (∞ : LegendreCompactCurve l)⟧) =
      (0 : Additive (FundamentalGroup (LegendreCompactCurve l) ∞)) := rfl
  rw [hclass, map_zero] at h
  exact h.symm

/-- Reversing a path from infinity changes the sign of its integral. -/
theorem legendrePathIntegral_symm_from_infty {l : LegendreParameter}
    (D : OriginalLegendreRealization l) {p : LegendreCompactCurve l}
    (γ : Path (∞ : LegendreCompactCurve l) p) :
    legendrePathIntegral D γ.symm = -legendrePathIntegral D γ := by
  have h := legendrePathIntegral_homotopic D (Path.Homotopic.trans_symm γ)
  rw [legendrePathIntegral_concat, legendrePathIntegral_refl_infty] at h
  apply eq_neg_iff_add_eq_zero.mpr
  exact (add_comm _ _).trans h

/-- All original path values differ from a selected value by exactly a period. -/
theorem legendrePathValues_eq_period_coset {l : LegendreParameter}
    (D : OriginalLegendreRealization l) {p : LegendreCompactCurve l}
    (γ₀ : Path (∞ : LegendreCompactCurve l) p) :
    Set.range (fun γ : Path (∞ : LegendreCompactCurve l) p => legendrePathIntegral D γ) =
      (fun z : ℂ => legendrePathIntegral D γ₀ + z) '' (legendrePeriods D : Set ℂ) := by
  ext z
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨legendrePathIntegral D (γ.trans γ₀.symm), ?_, ?_⟩
    · exact ⟨Additive.ofMul (FundamentalGroup.fromPath ⟦γ.trans γ₀.symm⟧),
        legendrePeriodHom_apply_loop D (γ.trans γ₀.symm)⟩
    · rw [legendrePathIntegral_concat, legendrePathIntegral_symm_from_infty]
      abel
  · rintro ⟨δ, hδ, rfl⟩
    change ∃ g, legendrePeriodHom D g = δ at hδ
    obtain ⟨g, hg⟩ := hδ
    obtain ⟨β, hβ⟩ := Quotient.exists_rep g.toMul.toPath
    have hclass : Additive.ofMul (FundamentalGroup.fromPath ⟦β⟧) = g :=
      congrArg (fun q => Additive.ofMul (FundamentalGroup.fromPath q)) hβ
    have hvalue := legendrePeriodHom_apply_loop D β
    rw [hclass] at hvalue
    refine ⟨β.trans γ₀, ?_⟩
    change legendrePathIntegral D (β.trans γ₀) = legendrePathIntegral D γ₀ + δ
    rw [legendrePathIntegral_concat, hvalue.symm.trans hg]
    exact add_comm _ _

/-- The original two-cycle period description, with its sole realization input explicit. -/
theorem originalEllipticPeriods_eq_two_generator_span
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) (a b : Path (∞ : LegendreCompactCurve l) ∞)
    (hgen : Subgroup.closure
      ({FundamentalGroup.fromPath ⟦a⟧, FundamentalGroup.fromPath ⟦b⟧} :
        Set (FundamentalGroup (LegendreCompactCurve l) ∞)) = ⊤) :
    originalEllipticPeriods hReal l = AddSubgroup.zmultiples (originalEllipticIntegral hReal l a) ⊔
      AddSubgroup.zmultiples (originalEllipticIntegral hReal l b) := by
  exact legendrePeriods_eq_two_generator_span (originalLegendreRealization hReal l) a b hgen

/-- A period is exactly an integer combination of the two actual cycle integrals. -/
theorem mem_originalEllipticPeriods_iff_integer_combination
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) (a b : Path (∞ : LegendreCompactCurve l) ∞)
    (hgen : Subgroup.closure
      ({FundamentalGroup.fromPath ⟦a⟧, FundamentalGroup.fromPath ⟦b⟧} :
        Set (FundamentalGroup (LegendreCompactCurve l) ∞)) = ⊤) (z : ℂ) :
    z ∈ originalEllipticPeriods hReal l ↔
      ∃ m n : ℤ, m • originalEllipticIntegral hReal l a +
        n • originalEllipticIntegral hReal l b = z := by
  rw [originalEllipticPeriods_eq_two_generator_span hReal l a b hgen, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨u, ⟨m, rfl⟩, v, ⟨n, rfl⟩, h⟩
    exact ⟨m, n, h⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m • originalEllipticIntegral hReal l a, ⟨m, rfl⟩,
      n • originalEllipticIntegral hReal l b, ⟨n, rfl⟩, h⟩

/-- The full original value coset, retaining every actual continuous path. -/
theorem originalEllipticIntegral_values_eq_period_coset
    (hReal : Unproved.Surfaces.OriginalLegendreAlgebraicRealization)
    (l : LegendreParameter) {p : LegendreCompactCurve l}
    (γ₀ : Path (∞ : LegendreCompactCurve l) p) :
    Set.range (fun γ : Path (∞ : LegendreCompactCurve l) p => originalEllipticIntegral hReal l γ) =
      (fun z : ℂ => originalEllipticIntegral hReal l γ₀ + z) ''
        (originalEllipticPeriods hReal l : Set ℂ) := by
  exact legendrePathValues_eq_period_coset (originalLegendreRealization hReal l) γ₀

end LowDimensionalTopology.Geometry.Surfaces
