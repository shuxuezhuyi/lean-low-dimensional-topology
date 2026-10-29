/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through the
credited convergence of actual conjugated matrix representatives;
see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalBookCoordinates

/-!
# Convergence of the original positive-c canonical matrices

Pointwise convergence of the actual intertwining homeomorphisms gives
convergent matrix representatives up to their determinant-one signs.
The positive lower-left entries of the first canonical matrices force
the signs to agree eventually. The final diagonal generator is not part
of this positive-c coordinate family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

namespace NormalizedCanonicalFuchsianModel

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
variable {m : MarkedRiemannSurface.{0, 0} R}

/-- The actual first positive-c matrices converge in their unchanged handle
and a/b order when their actual intertwining maps tend pointwise to identity. -/
theorem firstBookMatrix_tendsto_of_intertwining
    (P : NormalizedCanonicalFuchsianModel hg e m)
    {mn : ℕ → MarkedRiemannSurface.{0, 0} R}
    (Pn : ∀ n, NormalizedCanonicalFuchsianModel hg e (mn n))
    {Fn : ℕ → ℍ ≃ₜ ℍ}
    (hconv : ∀ z : ℍ, Tendsto (fun n => Fn n z) atTop (𝓝 z))
    (hintertwine : ∀ (n : ℕ) (d : Edge g) (z : ℍ),
      Fn n (P.matrices d • z) = (Pn n).matrices d • Fn n z)
    (i : Fin (g - 1)) (b : Fin 2) :
    Tendsto (fun n => (Pn n).firstBookMatrix i b) atTop (𝓝 (P.firstBookMatrix i b)) := by
  let γ := P.firstBookMatrix i b
  let δn := fun n => (Pn n).firstBookMatrix i b
  have hPact (z : ℍ) : γ • z = P.matrices (firstBookIndex i, b) • z := by
    change P.firstBookMatrix i b • z = _
    rcases P.firstBookMatrix_eq_or_neg i b with h | h
    · rw [h]
    · rw [h, LiZhongQC.s27v_c_neg_smul]
  have hPnact (n : ℕ) (z : ℍ) :
      δn n • z = (Pn n).matrices (firstBookIndex i, b) • z := by
    change (Pn n).firstBookMatrix i b • z = _
    rcases (Pn n).firstBookMatrix_eq_or_neg i b with h | h
    · rw [h]
    · rw [h, LiZhongQC.s27v_c_neg_smul]
  have hRn (n : ℕ) : LiZhongQC.RepresentsConj (Fn n) γ (δn n) := by
    intro z
    rw [hPnact n z, hPact ((Fn n).symm z)]
    simpa only [Homeomorph.apply_symm_apply] using
      (hintertwine n (firstBookIndex i, b) ((Fn n).symm z)).symm
  have hR : LiZhongQC.RepresentsConj (Homeomorph.refl ℍ) γ γ := fun _ => rfl
  obtain ⟨ε, hε, hεt⟩ := LiZhongQC.s27v_rep_tendsto
    (F := Homeomorph.refl ℍ) hconv hRn hR
  have hc : Tendsto (fun n => ε n 1 0) atTop (𝓝 (γ 1 0)) :=
    ((by fun_prop : Continuous
      (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 1 0)).tendsto γ).comp hεt
  have hpos : ∀ᶠ n in atTop, 0 < ε n 1 0 :=
    hc.eventually_const_lt (P.firstBookMatrix_lowerLeft_pos i b)
  have hsame : ε =ᶠ[atTop] δn := by
    filter_upwards [hpos] with n hn
    rcases hε n with h | h
    · exact h
    · have hentry : ε n 1 0 = -(δn n 1 0) := by
        simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] using
          congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 1 0) h
      have hPn := (Pn n).firstBookMatrix_lowerLeft_pos i b
      rw [hentry] at hn
      exact False.elim ((not_lt_of_ge (neg_nonpos.mpr hPn.le)) hn)
  exact hεt.congr' hsame

/-- The whole original first-coordinate family converges with exactly its
ordered a,c,d and a-prime,c-prime,d-prime entries. -/
theorem firstBookCoordinates_tendsto_of_intertwining
    (P : NormalizedCanonicalFuchsianModel hg e m)
    {mn : ℕ → MarkedRiemannSurface.{0, 0} R}
    (Pn : ∀ n, NormalizedCanonicalFuchsianModel hg e (mn n))
    {Fn : ℕ → ℍ ≃ₜ ℍ}
    (hconv : ∀ z : ℍ, Tendsto (fun n => Fn n z) atTop (𝓝 z))
    (hintertwine : ∀ (n : ℕ) (d : Edge g) (z : ℍ),
      Fn n (P.matrices d • z) = (Pn n).matrices d • Fn n z) :
    Tendsto (fun n => (Pn n).firstBookCoordinates) atTop (𝓝 P.firstBookCoordinates) := by
  have hcoords : Continuous
      (bookMatrixCoordinates : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℝ × ℝ × ℝ) := by
    change Continuous (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
      (A 0 0, A 1 0, A 1 1))
    fun_prop
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun n =>
    (bookMatrixCoordinates ((Pn n).firstBookMatrix i 0),
      bookMatrixCoordinates ((Pn n).firstBookMatrix i 1))) atTop
    (𝓝 (bookMatrixCoordinates (P.firstBookMatrix i 0),
      bookMatrixCoordinates (P.firstBookMatrix i 1)))
  exact ((hcoords.tendsto _).comp
    (P.firstBookMatrix_tendsto_of_intertwining Pn hconv hintertwine i 0)).prodMk_nhds
    ((hcoords.tendsto _).comp
      (P.firstBookMatrix_tendsto_of_intertwining Pn hconv hintertwine i 1))

end NormalizedCanonicalFuchsianModel

end LowDimensionalTopology.Geometry.Teichmuller
