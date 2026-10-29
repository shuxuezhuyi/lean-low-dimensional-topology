module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticGeodesicBigonInput
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

/-!
# The written quadratic-geodesic uniqueness argument on the actual native lift

The existing argument-principle polygon theorem gives at least three small
corners. Each genuine corner of either original local geodesic has the
existing zero-order angle lower bound, leaving only two joining vertices.
No bundled native existence or uniqueness input is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Real ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

/-- The source's actual argument-principle contradiction proves equality
of the two original local-geodesic traces, from finite geometry only. -/
theorem native_quadratic_geodesic_range_eq_of_bigon_inputs
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : ℍ} (α β : Path a b), a ≠ b →
        IsPhiGeodesicRS (qH : ℍ → ℂ → ℂ) α →
        IsPhiGeodesicRS (qH : ℍ → ℂ → ℂ) β → Set.range α = Set.range β := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α β hab hα hβ
  by_contra hne
  obtain ⟨c, r, hr, hmap, n, hn, hdata⟩ := hbigon hp α β hab hα hβ hne
  let := hn
  obtain ⟨P, E, _htrace, hE, hcorners⟩ := hdata
  let φ : ℂ → ℂ := fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w)
  have hA : Differentiable ℂ (fun w : ℂ => c + (r : ℂ) * w) := by fun_prop
  have hφ : DifferentiableOn ℂ φ unitDisc :=
    ((utm_liftQD_differentiableOn q.property hp).comp hA.differentiableOn hmap).const_mul _
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hφne : ∃ w ∈ unitDisc, φ w ≠ 0 := by
    refine ⟨P.side 0 (1 / 2), ?_, ?_⟩
    · apply P.closure_sub
      apply frontier_subset_closure
      rw [P.frontier_eq]
      exact mem_iUnion.mpr ⟨0, 1 / 2, Ioo_subset_Icc_self hhalf, rfl⟩
    · obtain ⟨θ, hθ⟩ := (P.side_straight 0).1
      exact (mul_ne_zero_iff.mp (hθ (1 / 2) hhalf).2.2.1).1
  let S : Set (Fin n) := {j | ∃ m : ℕ,
    meromorphicOrderAt φ (P.vert j) = (m : ℤ) ∧ P.angle j < 2 * π / ((m : ℝ) + 2)}
  have hcount : 3 ≤ S.ncard := thm25_2_polygon hφ hφne P
  have hsub : S ⊆ (E : Set (Fin n)) := by
    intro j hj
    by_contra hjE
    obtain ⟨m, hm, hsmall⟩ := hj
    obtain hc | hc := hcorners j hjE
    · have hlarge := hangle hp α hα c r hr hmap n P j 0 1 hc m hm
      exact (not_lt_of_ge hlarge) hsmall
    · have hlarge := hangle hp β hβ c r hr hmap n P j 0 1 hc m hm
      exact (not_lt_of_ge hlarge) hsmall
  have hupper : S.ncard ≤ 2 := by
    calc S.ncard ≤ (E : Set (Fin n)).ncard := Set.ncard_le_ncard hsub
      _ = E.card := Set.ncard_coe_finset E
      _ ≤ 2 := hE
  omega

end LowDimensionalTopology.Geometry.Teichmuller
