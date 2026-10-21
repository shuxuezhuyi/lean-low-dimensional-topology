/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperboloidBall.Distance
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Frame
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Hyperboloid isometries

Original proof with time orientation expressed by
preservation of the positive hyperboloid sheet. Every distance-preserving
map extends to one unique positive Lorentz matrix and is automatically onto.
-/

@[expose] public section
noncomputable section
open Set
open scoped MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

abbrev IsHyperboloidIsometry (f : Hyperboloid n → Hyperboloid n) : Prop :=
  @Isometry (Hyperboloid n) (Hyperboloid n)
    (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
    (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace f

theorem isHyperboloidIsometry_iff_dist (f : Hyperboloid n → Hyperboloid n) :
    IsHyperboloidIsometry f ↔ ∀ x y,hyperboloidPathDist (f x) (f y)=hyperboloidPathDist x y := by
  rw [IsHyperboloidIsometry,@isometry_iff_dist_eq (Hyperboloid n) (Hyperboloid n)
    (hyperboloidMetricSpace n).toPseudoMetricSpace (hyperboloidMetricSpace n).toPseudoMetricSpace]
  simp only [hyperboloidMetricSpace_dist]

theorem isHyperboloidIsometry_iff_preserves_form (f : Hyperboloid n → Hyperboloid n) :
    IsHyperboloidIsometry f ↔ ∀ x y,lorentzForm (f x).val (f y).val=lorentzForm x.val y.val := by
  rw [isHyperboloidIsometry_iff_dist]
  constructor
  · intro hf x y
    rw [← hyperboloidPathDist_cosh,← hyperboloidPathDist_cosh,hf]
  · intro hf x y
    apply Real.cosh_injOn (ENNReal.toReal_nonneg : 0≤hyperboloidPathDist (f x) (f y))
      (ENNReal.toReal_nonneg : 0≤hyperboloidPathDist x y)
    change Real.cosh (hyperboloidPathDist (f x) (f y))=Real.cosh (hyperboloidPathDist x y)
    rw [hyperboloidPathDist_cosh,hyperboloidPathDist_cosh,hf]

theorem hyperboloid_isometry_iff_lorentzMatrix (f : Hyperboloid n → Hyperboloid n) :
    IsHyperboloidIsometry f ↔ ∃ A : GL (Fin (n+1)) ℝ,A∈lorentzPositiveOrthogonalGroup n ∧
      ∀ x : Hyperboloid n,(f x).val=lorentzRowLinearMap A.val x.val := by
  constructor
  · intro hf
    exact hyperboloid_form_preserver_exists_lorentzMatrix f
      ((isHyperboloidIsometry_iff_preserves_form f).mp hf)
  · rintro ⟨A,hA,hf⟩
    apply (isHyperboloidIsometry_iff_preserves_form f).mpr
    intro x y
    rw [hf,hf]
    exact lorentzOrthogonal_preserves_form ((mem_lorentzPositiveOrthogonalGroup A).mp hA).1 _ _

theorem hyperboloid_isometry_bijective {f : Hyperboloid n → Hyperboloid n}
    (hf : IsHyperboloidIsometry f) : Function.Bijective f :=
  hyperboloid_form_preserver_bijective f ((isHyperboloidIsometry_iff_preserves_form f).mp hf)

def lorentzHyperboloidMap (A : lorentzPositiveOrthogonalGroup n) : Hyperboloid n → Hyperboloid n :=
  fun x=>⟨lorentzRowLinearMap A.val.val x.val,
    (lorentzOrthogonal_positive_iff_maps_sheet
      ((mem_lorentzPositiveOrthogonalGroup A.val).mp A.property).1).mp
      ((mem_lorentzPositiveOrthogonalGroup A.val).mp A.property).2 x.property⟩

theorem lorentzHyperboloidMap_isometry (A : lorentzPositiveOrthogonalGroup n) :
    IsHyperboloidIsometry (lorentzHyperboloidMap A) := by
  apply (hyperboloid_isometry_iff_lorentzMatrix _).mpr
  exact ⟨A.val,A.property,fun _=>rfl⟩

theorem lorentzHyperboloidMap_one :
    lorentzHyperboloidMap (1 : lorentzPositiveOrthogonalGroup n)=id := by
  funext x
  apply Subtype.ext
  exact lorentzRowLinearMap_one x.val

theorem lorentzHyperboloidMap_mul (A B : lorentzPositiveOrthogonalGroup n) (x : Hyperboloid n) :
    lorentzHyperboloidMap (A*B) x=lorentzHyperboloidMap B (lorentzHyperboloidMap A x) := by
  apply Subtype.ext
  exact lorentzRowLinearMap_mul A.val.val B.val.val x.val

def lorentzHyperboloidIsometryEquiv (A : lorentzPositiveOrthogonalGroup n) :
    @IsometryEquiv (Hyperboloid n) (Hyperboloid n)
      (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
      (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace :=
  @IsometryEquiv.mk (Hyperboloid n) (Hyperboloid n)
    (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
    (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
    { toFun:=lorentzHyperboloidMap A
      invFun:=lorentzHyperboloidMap A⁻¹
      left_inv x:=by rw [← lorentzHyperboloidMap_mul,mul_inv_cancel,lorentzHyperboloidMap_one]; rfl
      right_inv x:=by rw [← lorentzHyperboloidMap_mul,inv_mul_cancel,lorentzHyperboloidMap_one]; rfl }
    (lorentzHyperboloidMap_isometry A)

theorem hyperboloid_isometry_iff_raw_lorentzMatrix (f : Hyperboloid n → Hyperboloid n) :
    IsHyperboloidIsometry f ↔
      ∃ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
        (∀ v : LorentzVector n,lorentzForm (lorentzRowLinearMap M v)
          (lorentzRowLinearMap M v)=lorentzForm v v) ∧ 0<M 0 0 ∧
        ∀ x : Hyperboloid n,(f x).val=lorentzRowLinearMap M x.val := by
  rw [hyperboloid_isometry_iff_lorentzMatrix]
  constructor
  · rintro ⟨A,hA,hf⟩
    obtain ⟨hO,hp⟩:=(mem_lorentzPositiveOrthogonalGroup A).mp hA
    exact ⟨A.val,fun v=>lorentzOrthogonal_preserves_form hO v v,hp,hf⟩
  · rintro ⟨M,hM,hp,hf⟩
    obtain ⟨A,hA,rfl⟩:=lorentz_quadratic_preserver_exists_group M hM
    exact ⟨A,(mem_lorentzPositiveOrthogonalGroup A).mpr ⟨hA,hp⟩,hf⟩

theorem lorentzRowLinearMap_injective (n : ℕ) :
    Function.Injective (lorentzRowLinearMap (n:=n)) := by
  intro A B h
  apply Matrix.toLinearMapRight'.injective
  apply LinearMap.ext
  intro v
  have he:=congrArg (fun T : LorentzVector n →ₗ[ℝ] LorentzVector n=>
    lorentzCoordinates n (T ((lorentzCoordinates n).symm v))) h
  simpa only [lorentzRowLinearMap_coordinates,LinearEquiv.apply_symm_apply,
    Matrix.toLinearMapRight'_apply] using he

theorem lorentzHyperboloidMap_injective (n : ℕ) :
    Function.Injective (lorentzHyperboloidMap (n:=n)) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  apply lorentzRowLinearMap_injective n
  have hA:=hyperboloidFrameExtension_unique (lorentzHyperboloidMap A)
    (lorentzRowLinearMap A.val.val) (fun _=>rfl)
  have hB:=hyperboloidFrameExtension_unique (lorentzHyperboloidMap B)
    (lorentzRowLinearMap B.val.val) (fun _=>rfl)
  rw [h] at hA
  exact hA.trans hB.symm

theorem hyperboloid_isometry_existsUnique_lorentzMatrix
    {f : Hyperboloid n → Hyperboloid n} (hf : IsHyperboloidIsometry f) :
    ∃! A : lorentzPositiveOrthogonalGroup n,
      ∀ x : Hyperboloid n,(f x).val=lorentzRowLinearMap A.val.val x.val := by
  obtain ⟨A,hA,he⟩:=(hyperboloid_isometry_iff_lorentzMatrix f).mp hf
  refine ⟨⟨A,hA⟩,he,?_⟩
  intro B hB
  apply lorentzHyperboloidMap_injective n
  funext x
  apply Subtype.ext
  exact (hB x).symm.trans (he x)

end LowDimensionalTopology.Geometry.Hyperbolic
