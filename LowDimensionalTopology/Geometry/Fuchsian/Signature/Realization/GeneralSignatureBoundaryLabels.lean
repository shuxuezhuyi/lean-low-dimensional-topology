/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The three literal side positions of each boundary block, in the original
frozen canonical polygon. Position one is the cut; zero and two are true sides. -/
def generalCoreBoundarySideIndex (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) (r : Fin 3) : Fin (generalCoreAngles g orders s t).length :=
  ⟨(cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0)).length + 3 * j.val + r.val, by
    have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
      (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) t)
    rw [hlen]
    have hj := j.isLt
    have hr := r.isLt
    omega⟩

theorem generalCoreBoundarySideIndex_cut_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) (r : Fin 3) :
    generalCoreIsCutSide g orders s t (generalCoreBoundarySideIndex g orders s t j r) ↔ r = 1 := by
  let p := (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length
  have hr := r.isLt
  change (p ≤ p + 3 * j.val + r.val ∧ (p + 3 * j.val + r.val - p) % 3 = 1) ↔ r = 1
  constructor
  · intro h
    apply Fin.ext
    change r.val = 1
    omega
  · intro h
    subst r
    omega

theorem generalCoreBoundarySideIndex_next_zero (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) :
    finRotate _ (generalCoreBoundarySideIndex g orders s t j 0) =
      generalCoreBoundarySideIndex g orders s t j 1 := by
  have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
    (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0) t)
  have hj := j.isLt
  apply Fin.ext
  rw [generalSignatureAux_finRotate_val]
  change (if _ + 3 * j.val + 0 + 1 = _ then 0 else _ + 3 * j.val + 0 + 1) = _ + 3 * j.val + 1
  rw [ite_eq_right (by omega)]

theorem generalCoreBoundarySideIndex_next_one (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) :
    finRotate _ (generalCoreBoundarySideIndex g orders s t j 1) =
      generalCoreBoundarySideIndex g orders s t j 2 := by
  have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
    (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0) t)
  have hj := j.isLt
  apply Fin.ext
  rw [generalSignatureAux_finRotate_val]
  change (if _ + 3 * j.val + 1 + 1 = _ then 0 else _ + 3 * j.val + 1 + 1) = _ + 3 * j.val + 2
  rw [ite_eq_right (by omega)]

theorem generalCoreBoundarySideIndex_pair_zero (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) :
    generalCoreAuxPairing g orders s t (generalCoreBoundarySideIndex g orders s t j 0) =
      generalCoreBoundarySideIndex g orders s t j 2 := by
  let p := (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length
  apply Fin.ext
  rw [generalCoreAuxPairing_val]
  change (if p + 3 * j.val + 0 < p then _ else _) = p + 3 * j.val + 2
  rw [ite_eq_right (by omega)]
  change p + generalSignatureAuxBoundaryPairNat (p + 3 * j.val + 0 - p) = p + 3 * j.val + 2
  rw [show p + 3 * j.val + 0 - p = 3 * j.val by omega,
    generalSignatureAuxBoundaryPairNat_zero]
  omega

theorem generalCoreBoundarySideIndex_pair_one (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) :
    generalCoreAuxPairing g orders s t (generalCoreBoundarySideIndex g orders s t j 1) =
      generalCoreBoundarySideIndex g orders s t j 1 := by
  let p := (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length
  apply Fin.ext
  rw [generalCoreAuxPairing_val]
  change (if p + 3 * j.val + 1 < p then _ else _) = p + 3 * j.val + 1
  rw [ite_eq_right (by omega)]
  change p + generalSignatureAuxBoundaryPairNat (p + 3 * j.val + 1 - p) = p + 3 * j.val + 1
  rw [show p + 3 * j.val + 1 - p = 3 * j.val + 1 by omega,
    generalSignatureAuxBoundaryPairNat_one]
  omega

theorem generalCoreIsCutSide_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) :
    generalCoreIsCutSide g orders s t i ↔
      ∃ j : Fin t, i = generalCoreBoundarySideIndex g orders s t j 1 := by
  let p := (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length
  have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
    (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0) t)
  constructor
  · intro hi
    change p ≤ i.val ∧ (i.val - p) % 3 = 1 at hi
    have hiLt := i.isLt
    let j : Fin t := ⟨(i.val - p) / 3, by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    change i.val = p + 3 * ((i.val - p) / 3) + 1
    omega
  · rintro ⟨j, rfl⟩
    exact (generalCoreBoundarySideIndex_cut_iff g orders s t j 1).mpr rfl

theorem generalCoreAuxPairing_isCut_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) :
    generalCoreIsCutSide g orders s t (generalCoreAuxPairing g orders s t i) ↔
      generalCoreIsCutSide g orders s t i := by
  have hself (k : Fin (generalCoreAngles g orders s t).length)
      (hk : generalCoreIsCutSide g orders s t k) : generalCoreAuxPairing g orders s t k = k := by
    obtain ⟨j, rfl⟩ := (generalCoreIsCutSide_iff g orders s t k).mp hk
    exact generalCoreBoundarySideIndex_pair_one g orders s t j
  constructor
  · intro hi
    have heq := hself _ hi
    rw [generalCoreAuxPairing_involutive g orders s t i] at heq
    exact heq.symm ▸ hi
  · intro hi
    rw [hself i hi]
    exact hi

theorem generalCoreBoundarySideIndex_angle (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin t) (r : Fin 3) :
    generalCoreTheta g orders s t (generalCoreBoundarySideIndex g orders s t j r) =
      if r = 0 then generalCoreBaseAngle g orders s t else Real.pi / 2 := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let p := (cofiniteConstructionSideAngles β g ms).length
  let a := p + 3 * j.val + r.val
  have hget (n : ℕ) : (generalCoreAngles g orders s t).getD n β =
      (generalSignatureAuxAngleList β g ms t).getD n β :=
    congrArg (fun L : List ℝ => L.getD n β) (generalCoreAngles_eq_auxAngleList g orders s t)
  change (generalCoreAngles g orders s t)[generalCoreBoundarySideIndex g orders s t j r] = _
  simp only [Fin.getElem_fin]
  rw [← List.getD_eq_getElem _ β (generalCoreBoundarySideIndex g orders s t j r).isLt]
  change (generalCoreAngles g orders s t).getD a β = _
  rw [hget, generalSignatureAuxAngleList, List.getD_append_right _ _ _ _ (by omega)]
  rw [show a - (cofiniteConstructionSideAngles β g ms).length = 3 * j.val + r.val by
      dsimp only [a, p]; omega, generalSignatureAuxBoundaryAngles_getD]
  have hj := j.isLt
  have hr := r.isLt
  by_cases hr0 : r = 0
  · subst r
    simp [β]
  · have hrN : r.val ≠ 0 := by intro h; apply hr0; exact Fin.ext h
    rw [ite_eq_left (by omega), ite_eq_right hr0]

theorem generalCoreTargetGenerator_mem (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
    (i : Fin (generalCoreAngles g orders s t).length) (hi : ¬ generalCoreIsCutSide g orders s t i) :
    generalCoreTargetGenerator g orders s t ho hdef d hd hb i ∈
      generalCoreTargetGroup g orders s t ho hdef d hd hb :=
  Subgroup.subset_closure (mem_range.mpr ⟨⟨i, hi⟩, rfl⟩)

/-- Every retained genuine original side map belongs to the actual target subgroup. -/
theorem generalCoreAuxSidePairing_element_mem_target (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
    (a : (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
      (generalCoreTheta_mem g orders s t ho hdef) hd hb)).Side)
    (ha : ¬ generalCoreIsCutSide g orders s t ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm a)) :
    (generalCoreAuxSidePairing g orders s t ho hdef d hd hb).element a ∈
      generalCoreTargetGroup g orders s t ho hdef d hd hb := by
  change generalCoreTargetGenerator g orders s t ho hdef d hd hb
    ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm a) ∈ _
  exact generalCoreTargetGenerator_mem g orders s t ho hdef d hd hb _ ha

/-- The boundary translation is one of the actual retained generators of H. -/
theorem generalCoreBoundarySideIndex_generator_mem (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
    (j : Fin t) :
    generalCoreTargetGenerator g orders s t ho hdef d hd hb (generalCoreBoundarySideIndex g orders s t j 0) ∈
      generalCoreTargetGroup g orders s t ho hdef d hd hb := by
  apply Subgroup.subset_closure
  refine mem_range.mpr ⟨⟨generalCoreBoundarySideIndex g orders s t j 0, ?_⟩, rfl⟩
  rw [generalCoreBoundarySideIndex_cut_iff]
  decide

end LowDimensionalTopology.Geometry.Fuchsian
