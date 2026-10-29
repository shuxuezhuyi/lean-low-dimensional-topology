module

public import LowDimensionalTopology.Geometry.SeveralComplexVariables.InjectiveHolomorphicFiberSlice
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Selected original finite complex coordinates

Only permutations of the original finite coordinates and the native
head/tail product equivalence are used. The transported map remains the
original map between its actual transported domains.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- Separate one selected original coordinate, retaining all other coordinates. -/
def selectedFiniteComplexCoordinates {m : ℕ} (i : Fin (m + 1)) :
    (Fin (m + 1) → ℂ) ≃L[ℂ] (ℂ × (Fin m → ℂ)) :=
  ((ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (m + 1) => ℂ)
    (Equiv.swap 0 i)).symm).trans (Fin.consEquivL ℂ (fun _ : Fin (m + 1) => ℂ)).symm

/-- The distinguished coordinate is the selected original coordinate. -/
theorem selectedFiniteComplexCoordinates_fst {m : ℕ} (i : Fin (m + 1))
    (z : Fin (m + 1) → ℂ) : (selectedFiniteComplexCoordinates i z).1 = z i := by
  change z (Equiv.swap (0 : Fin (m + 1)) i 0) = z i
  rw [Equiv.swap_apply_left]

/-- The distinguished coordinate direction is the selected original standard basis vector. -/
theorem selectedFiniteComplexCoordinates_single {m : ℕ} (i : Fin (m + 1)) :
    selectedFiniteComplexCoordinates i (Pi.single i 1) = (1, 0) := by
  apply Prod.ext
  · rw [selectedFiniteComplexCoordinates_fst, Pi.single_eq_same]
  · funext j
    change (Pi.single i (1 : ℂ) : Fin (m + 1) → ℂ)
      (Equiv.swap (0 : Fin (m + 1)) i j.succ) = 0
    have hne : Equiv.swap (0 : Fin (m + 1)) i j.succ ≠ i := by
      intro h
      have hzero : j.succ = 0 := (Equiv.swap (0 : Fin (m + 1)) i).injective
        (h.trans (Equiv.swap_apply_left (0 : Fin (m + 1)) i).symm)
      exact Fin.succ_ne_zero j hzero
    exact Pi.single_eq_of_ne hne 1

/-- Inverse-coordinate transport of the selected direction. -/
theorem selectedFiniteComplexCoordinates_symm_one {m : ℕ} (i : Fin (m + 1)) :
    (selectedFiniteComplexCoordinates i).symm (1, 0) = Pi.single i 1 := by
  apply (selectedFiniteComplexCoordinates i).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, selectedFiniteComplexCoordinates_single]

/-- An injective analytic map with nonzero derivative has injective derivative,
assuming the corresponding statement in one lower dimension. -/
theorem fderiv_injective_of_fderiv_ne_zero {m : ℕ}
    (ih : ∀ (V : Set (Fin m → ℂ)), IsOpen V → IsPreconnected V →
      ∀ (K : (Fin m → ℂ) → (Fin m → ℂ)), AnalyticOnNhd ℂ K V → Set.InjOn K V →
        ∀ w ∈ V, Function.Injective (fderiv ℂ K w))
    {D : Set (Fin (m + 1) → ℂ)} (hD : IsOpen D)
    {a : Fin (m + 1) → ℂ} (ha : a ∈ D)
    {F : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ)}
    (hF : AnalyticOnNhd ℂ F D) (hInj : Set.InjOn F D)
    (hDF : fderiv ℂ F a ≠ 0) :
    Function.Injective (fderiv ℂ F a) := by
  classical
  have hentryExists : ∃ i j : Fin (m + 1),
      (fderiv ℂ F a) (Pi.single j 1) i ≠ 0 := by
    by_contra h
    have hentries (i j : Fin (m + 1)) : (fderiv ℂ F a) (Pi.single j 1) i = 0 := by
      by_contra hij
      exact h ⟨i, j, hij⟩
    have hmatrix : LinearMap.toMatrix' (fderiv ℂ F a).toLinearMap = 0 := by
      funext i j
      exact hentries i j
    have hlinear : (fderiv ℂ F a).toLinearMap = 0 :=
      LinearMap.toMatrix'.injective (hmatrix.trans (map_zero LinearMap.toMatrix').symm)
    apply hDF
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg
      (fun L : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ) => L v) hlinear
  obtain ⟨i, j, hentry⟩ := hentryExists
  let S : ((Fin m → ℂ) × ℂ) ≃L[ℂ] (Fin (m + 1) → ℂ) :=
    (ContinuousLinearEquiv.prodComm ℂ (Fin m → ℂ) ℂ).trans
      (selectedFiniteComplexCoordinates j).symm
  let R : (Fin (m + 1) → ℂ) ≃L[ℂ] (ℂ × (Fin m → ℂ)) :=
    selectedFiniteComplexCoordinates i
  let V : Set ((Fin m → ℂ) × ℂ) := S ⁻¹' D
  let G : ((Fin m → ℂ) × ℂ) → (ℂ × (Fin m → ℂ)) := R ∘ F ∘ S
  let b : (Fin m → ℂ) × ℂ := S.symm a
  have hSb : S b = a := S.apply_symm_apply a
  have hb : b ∈ V := by
    change S b ∈ D
    rw [hSb]
    exact ha
  have hV : IsOpen V := hD.preimage S.continuous
  have hG : AnalyticOnNhd ℂ G V := by
    intro z hz
    have hsz : AnalyticAt ℂ S z :=
      (S : ((Fin m → ℂ) × ℂ) →L[ℂ] (Fin (m + 1) → ℂ)).analyticAt z
    exact ((R : (Fin (m + 1) → ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))).analyticAt
      (F (S z))).comp (f := fun x : ((Fin m → ℂ) × ℂ) => F (S x)) (x := z)
        ((hF (S z) hz).comp hsz)
  have hGInj : Set.InjOn G V := by
    intro x hx y hy hxy
    exact S.injective (hInj hx hy (R.injective hxy))
  have hGFD : HasFDerivAt G
      ((R : (Fin (m + 1) → ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))).comp
        ((fderiv ℂ F (S b)).comp
          (S : ((Fin m → ℂ) × ℂ) →L[ℂ] (Fin (m + 1) → ℂ)))) b :=
    (R : (Fin (m + 1) → ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))).hasFDerivAt.comp b
      ((hF (S b) hb).differentiableAt.hasFDerivAt.comp b
        (S : ((Fin m → ℂ) × ℂ) →L[ℂ] (Fin (m + 1) → ℂ)).hasFDerivAt)
  have hGlinear : fderiv ℂ G b =
      (R : (Fin (m + 1) → ℂ) →L[ℂ] (ℂ × (Fin m → ℂ))).comp
        ((fderiv ℂ F a).comp
          (S : ((Fin m → ℂ) × ℂ) →L[ℂ] (Fin (m + 1) → ℂ))) := by
    have h := hGFD.fderiv
    rwa [hSb] at h
  have hSone : S (0, 1) = Pi.single j 1 :=
    selectedFiniteComplexCoordinates_symm_one j
  have hpartial : ((fderiv ℂ G b) (0, 1)).1 ≠ 0 := by
    rw [hGlinear]
    change (selectedFiniteComplexCoordinates i ((fderiv ℂ F a) (S (0, 1)))).1 ≠ 0
    rw [hSone, selectedFiniteComplexCoordinates_fst]
    exact hentry
  have hDGi : Function.Injective (fderiv ℂ G b) :=
    fderiv_injective_of_first_partial_ne_zero ih hV hb hG hGInj hpartial
  intro v w hvw
  apply S.symm.injective
  apply hDGi
  rw [hGlinear]
  change R ((fderiv ℂ F a) (S (S.symm v))) =
    R ((fderiv ℂ F a) (S (S.symm w)))
  rw [S.apply_symm_apply, S.apply_symm_apply, hvw]

end LowDimensionalTopology.Geometry.SeveralComplexVariables
