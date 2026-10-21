/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.LorentzGroup
public import Mathlib.LinearAlgebra.BilinearForm.Hom

@[expose] public section

open Set Matrix Module
open scoped MatrixGroups InnerProductSpace

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

def lorentzBilinear (n : ℕ) : LinearMap.BilinForm ℝ (LorentzVector n) where
  toFun x :=
    { toFun := lorentzForm x
      map_add' y z := by simp [lorentzForm, inner_add_right]; ring
      map_smul' r y := by simp [lorentzForm, inner_smul_right]; ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change lorentzForm (x + y) z = lorentzForm x z + lorentzForm y z
    simp [lorentzForm, inner_add_left]
    ring
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    change lorentzForm (r • x) z = r * lorentzForm x z
    simp [lorentzForm, inner_smul_left]
    ring

theorem lorentzBilinear_apply {n : ℕ} (x y : LorentzVector n) :
    lorentzBilinear n x y = lorentzForm x y := rfl

theorem lorentzForm_eq_zero_of_forall {n : ℕ} {x : LorentzVector n}
    (h : ∀ y, lorentzForm x y = 0) : x = 0 := by
  have ht : x.1 = 0 := by simpa [lorentzForm] using h (1, 0)
  have hv : ‖x.2‖ ^ 2 = 0 := by
    have hh : -(‖x.2‖ ^ 2) = 0 := by simpa [lorentzForm] using h (0, x.2)
    exact neg_eq_zero.mp hh
  exact Prod.ext ht (norm_eq_zero.mp (sq_eq_zero_iff.mp hv))

theorem lorentzForm_ext_left {n : ℕ} {x z : LorentzVector n}
    (h : ∀ y, lorentzForm x y = lorentzForm z y) : x = z := by
  apply sub_eq_zero.mp
  apply lorentzForm_eq_zero_of_forall
  intro y
  change lorentzBilinear n (x - z) y = 0
  rw [map_sub, LinearMap.sub_apply, lorentzBilinear_apply, lorentzBilinear_apply, h y, sub_self]

/-- Coordinates in a basis consisting entirely of points on the positive sheet. -/
def hyperboloidFrameCoordinates (n : ℕ) : LorentzVector n ≃ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.cons (x.1 - Real.sqrt 2 * ∑ i, x.2 i) (fun i => x.2 i)
  invFun v := (v 0 + Real.sqrt 2 * ∑ i : Fin n, v i.succ,
    WithLp.toLp 2 (fun i => v i.succ))
  left_inv x := by
    apply Prod.ext
    · change x.1 - Real.sqrt 2 * ∑ i, x.2 i + Real.sqrt 2 * ∑ i, x.2 i = x.1
      ring
    · ext i; rfl
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change v 0 + Real.sqrt 2 * ∑ i : Fin n, v i.succ -
        Real.sqrt 2 * ∑ i : Fin n, v i.succ = v 0
      ring
    · rfl
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Prod.fst_add, Prod.snd_add, PiLp.add_apply,
        Finset.sum_add_distrib, Pi.add_apply]
      ring
    · rfl
  map_smul' r x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change r * x.1 - Real.sqrt 2 * ∑ i, r * x.2 i =
        r * (x.1 - Real.sqrt 2 * ∑ i, x.2 i)
      rw [← Finset.mul_sum]
      ring
    · rfl

def hyperboloidFrameBasis (n : ℕ) : Basis (Fin (n + 1)) ℝ (LorentzVector n) :=
  Basis.ofEquivFun (hyperboloidFrameCoordinates n)

theorem hyperboloidFrameBasis_zero (n : ℕ) :
    hyperboloidFrameBasis n 0 = lorentzTimeUnit n := by
  rw [hyperboloidFrameBasis, Basis.coe_ofEquivFun]
  apply Prod.ext
  · simp [hyperboloidFrameCoordinates, lorentzTimeUnit, Fin.succ_ne_zero]
  · ext i
    simp [hyperboloidFrameCoordinates, lorentzTimeUnit, Fin.succ_ne_zero]

theorem hyperboloidFrameBasis_succ (n : ℕ) (i : Fin n) :
    hyperboloidFrameBasis n i.succ =
      (Real.sqrt 2, WithLp.toLp 2 (Pi.single i 1)) := by
  rw [hyperboloidFrameBasis, Basis.coe_ofEquivFun]
  apply Prod.ext
  · simp [hyperboloidFrameCoordinates, Pi.single_apply, Fin.succ_inj]
  · ext j
    simp [hyperboloidFrameCoordinates, Pi.single_apply, Fin.succ_inj]

theorem hyperboloidFrameBasis_mem (n : ℕ) (i : Fin (n + 1)) :
    hyperboloidFrameBasis n i ∈ hyperboloidSet n := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [hyperboloidFrameBasis_zero]
    exact lorentzTimeUnit_mem n
  · rw [hyperboloidFrameBasis_succ]
    constructor
    · norm_num [lorentzForm, Real.sq_sqrt, ← pow_two]
    · exact Real.sqrt_pos.mpr (by norm_num)

def hyperboloidFrame (n : ℕ) (i : Fin (n + 1)) : Hyperboloid n :=
  ⟨hyperboloidFrameBasis n i, hyperboloidFrameBasis_mem n i⟩

/-- A linear extension defined solely from the values on the positive-sheet frame. -/
def hyperboloidFrameExtension {n : ℕ} (f : Hyperboloid n → Hyperboloid n) :
    LorentzVector n →ₗ[ℝ] LorentzVector n :=
  (hyperboloidFrameBasis n).constr ℝ (fun i => (f (hyperboloidFrame n i)).val)

theorem hyperboloidFrameExtension_frame {n : ℕ} (f : Hyperboloid n → Hyperboloid n)
    (i : Fin (n + 1)) :
    hyperboloidFrameExtension f (hyperboloidFrameBasis n i) = (f (hyperboloidFrame n i)).val := by
  exact (hyperboloidFrameBasis n).constr_basis ℝ _ i

theorem hyperboloidFrameExtension_preserves_form {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val)
    (x y : LorentzVector n) :
    lorentzForm (hyperboloidFrameExtension f x) (hyperboloidFrameExtension f y) =
      lorentzForm x y := by
  have he : (lorentzBilinear n).comp (hyperboloidFrameExtension f)
      (hyperboloidFrameExtension f) = lorentzBilinear n := by
    apply LinearMap.BilinForm.ext_basis (hyperboloidFrameBasis n)
    intro i j
    change lorentzForm (hyperboloidFrameExtension f (hyperboloidFrameBasis n i))
      (hyperboloidFrameExtension f (hyperboloidFrameBasis n j)) = _
    rw [hyperboloidFrameExtension_frame, hyperboloidFrameExtension_frame]
    exact hf (hyperboloidFrame n i) (hyperboloidFrame n j)
  exact congrArg (fun B : LinearMap.BilinForm ℝ (LorentzVector n) => B x y) he

theorem hyperboloidFrameExtension_injective {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val) :
    Function.Injective (hyperboloidFrameExtension f) := by
  intro x z hxz
  apply lorentzForm_ext_left
  intro y
  rw [← hyperboloidFrameExtension_preserves_form f hf x y,
    ← hyperboloidFrameExtension_preserves_form f hf z y, hxz]

theorem hyperboloidFrameExtension_surjective {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val) :
    Function.Surjective (hyperboloidFrameExtension f) :=
  LinearMap.surjective_of_injective (hyperboloidFrameExtension_injective f hf)

theorem hyperboloidFrameExtension_eq {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val)
    (x : Hyperboloid n) : hyperboloidFrameExtension f x.val = (f x).val := by
  have hp : ∀ y : LorentzVector n,
      lorentzForm (f x).val (hyperboloidFrameExtension f y) = lorentzForm x.val y := by
    have he : ((lorentzBilinear n) (f x).val).comp (hyperboloidFrameExtension f) =
        lorentzBilinear n x.val := by
      apply (hyperboloidFrameBasis n).ext
      intro i
      change lorentzForm (f x).val
        (hyperboloidFrameExtension f (hyperboloidFrameBasis n i)) = _
      rw [hyperboloidFrameExtension_frame]
      exact hf x (hyperboloidFrame n i)
    exact fun y => congrArg (fun l : LorentzVector n →ₗ[ℝ] ℝ => l y) he
  apply lorentzForm_ext_left
  intro z
  obtain ⟨y, rfl⟩ := hyperboloidFrameExtension_surjective f hf z
  rw [hyperboloidFrameExtension_preserves_form f hf, hp]

theorem hyperboloidFrameExtension_unique {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (T : LorentzVector n →ₗ[ℝ] LorentzVector n)
    (hT : ∀ x : Hyperboloid n, T x.val = (f x).val) :
    T = hyperboloidFrameExtension f := by
  apply (hyperboloidFrameBasis n).ext
  intro i
  rw [hyperboloidFrameExtension_frame]
  exact hT (hyperboloidFrame n i)

/-- The row-vector matrix of an arbitrary native Lorentz linear endomorphism. -/
def lorentzRowMatrix {n : ℕ} (T : LorentzVector n →ₗ[ℝ] LorentzVector n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (LinearMap.toMatrix' ((lorentzCoordinates n).toLinearMap.comp
    (T.comp (lorentzCoordinates n).symm.toLinearMap)))ᵀ

theorem lorentzRowLinearMap_rowMatrix {n : ℕ}
    (T : LorentzVector n →ₗ[ℝ] LorentzVector n) :
    lorentzRowLinearMap (lorentzRowMatrix T) = T := by
  apply LinearMap.ext
  intro x
  apply (lorentzCoordinates n).injective
  rw [lorentzRowLinearMap_coordinates, ← Matrix.mulVec_transpose]
  simp [lorentzRowMatrix, LinearMap.toMatrix'_mulVec]

theorem hyperboloid_form_preserver_exists_lorentzMatrix {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val) :
    ∃ A : GL (Fin (n + 1)) ℝ, A ∈ lorentzPositiveOrthogonalGroup n ∧
      ∀ x : Hyperboloid n, (f x).val = lorentzRowLinearMap A.val x.val := by
  let M := lorentzRowMatrix (hyperboloidFrameExtension f)
  have hM : ∀ x : LorentzVector n,
      lorentzForm (lorentzRowLinearMap M x) (lorentzRowLinearMap M x) = lorentzForm x x := by
    rw [show lorentzRowLinearMap M = hyperboloidFrameExtension f from
      lorentzRowLinearMap_rowMatrix _]
    exact fun x => hyperboloidFrameExtension_preserves_form f hf x x
  obtain ⟨A, hA, hAM⟩ := lorentz_quadratic_preserver_exists_group M hM
  have he : ∀ x : Hyperboloid n, lorentzRowLinearMap A.val x.val = (f x).val := by
    intro x
    rw [hAM, show lorentzRowLinearMap M = hyperboloidFrameExtension f from
      lorentzRowLinearMap_rowMatrix _]
    exact hyperboloidFrameExtension_eq f hf x
  refine ⟨A, ?_, fun x => (he x).symm⟩
  rw [mem_lorentzPositiveOrthogonalGroup]
  refine ⟨hA, (lorentzOrthogonal_positive_iff_maps_sheet hA).mpr ?_⟩
  intro x hx
  rw [he ⟨x, hx⟩]
  exact (f ⟨x, hx⟩).property

theorem hyperboloid_form_preserver_bijective {n : ℕ}
    (f : Hyperboloid n → Hyperboloid n)
    (hf : ∀ x y, lorentzForm (f x).val (f y).val = lorentzForm x.val y.val) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hyperboloidFrameExtension_injective f hf
    rw [hyperboloidFrameExtension_eq f hf, hyperboloidFrameExtension_eq f hf, hxy]
  · obtain ⟨A, hA, hfA⟩ := hyperboloid_form_preserver_exists_lorentzMatrix f hf
    obtain ⟨hO, hpos⟩ := (mem_lorentzPositiveOrthogonalGroup A).mp hA
    have himg := (lorentzOrthogonal_positive_iff_sheet_image hO).mp hpos
    intro y
    have hy : y.val ∈ lorentzRowLinearMap A.val '' hyperboloidSet n := by
      rw [himg]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    rw [hfA]
    exact hxy

end
end LowDimensionalTopology.Geometry.Hyperbolic
