/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundaryWedge
public import LowDimensionalTopology.External.TauCeti.Topology.Homotopy.Path
public import Mathlib.Data.List.OfFn
public import Mathlib.Topology.Subpath
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

/-- The fundamental-group class of an actual based loop. -/
def pathClass {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) :
    FundamentalGroup X x := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)

/-- The actual based loop class, exposed through the public path-quotient constructor. -/
theorem pathClass_eq_fromPath {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) :
    pathClass p = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := rfl

@[simp] theorem pathClass_refl {X : Type*} [TopologicalSpace X] (x : X) :
    pathClass (Path.refl x) = 1 := rfl

@[simp] theorem pathClass_symm {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) : pathClass p.symm = (pathClass p)⁻¹ := rfl

/-- Mathlib's endomorphism-group product reverses chronological path concatenation. -/
theorem pathClass_trans {X : Type*} [TopologicalSpace X] {x : X}
    (p q : Path x x) : pathClass (p.trans q) = pathClass q * pathClass p := rfl

private def basedSubpath {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) (a b : unitInterval) (ha : p a = x) (hb : p b = x) : Path x x :=
  (p.subpath a b).cast ha.symm hb.symm

private theorem basedSubpath_self {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) (a : unitInterval) (ha : p a = x) :
    basedSubpath p a a ha ha = Path.refl x := by
  ext t
  simpa [basedSubpath, Path.subpath, Icc.convexComb_eq] using ha

private theorem basedSubpath_class_trans {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) (a b c : unitInterval)
    (ha : p a = x) (hb : p b = x) (hc : p c = x) :
    pathClass (basedSubpath p a c ha hc) =
      pathClass (basedSubpath p b c hb hc) * pathClass (basedSubpath p a b ha hb) := by
  apply CategoryTheory.End.ext
  exact (Path.Homotopic.Quotient.subpath_cast_trans p a b c ha.symm hb.symm hc.symm).symm

/-- Taking inverses restores the chronological order of a subdivided based loop. -/
private theorem inverse_subdivision {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (ht : ∀ k, p (t k) = x) :
    (List.ofFn fun k : Fin n =>
      (pathClass (basedSubpath p (t k.castSucc) (t k.succ)
        (ht k.castSucc) (ht k.succ)))⁻¹).prod =
      (pathClass (basedSubpath p (t 0) (t (Fin.last n)) (ht 0) (ht (Fin.last n))))⁻¹ := by
  induction n with
  | zero => simp [basedSubpath_self]
  | succ n ih =>
    rw [List.ofFn_succ', List.prod_concat]
    have hcast (i : Fin n) : i.succ.castSucc = i.castSucc.succ := by
      apply Fin.ext
      rfl
    have hi := ih (fun k => t k.castSucc) (fun k => ht k.castSucc)
    simp only [hcast] at hi
    rw [hi]
    rw [basedSubpath_class_trans p (t 0) (t (Fin.last n).castSucc)
      (t (Fin.last (n + 1))) (ht 0) (ht (Fin.last n).castSucc) (ht (Fin.last (n + 1))),
      mul_inv_rev]
    simp only [Fin.castSucc_zero, Fin.succ_last]

/-- The geometric boundary circle traversed exactly once counterclockwise. -/
def boundaryLoop (g : ℕ) : Path (boundaryBase g) (boundaryBase g) where
  toFun t := ⟨projection g (handleBoundaryPoint t.val),
    ⟨_, handleBoundaryPoint_norm _, rfl⟩⟩
  continuous_toFun := ((projection_continuous g).comp
    (handleBoundaryPoint_continuous.comp continuous_subtype_val)).subtype_mk _
  source' := rfl
  target' := by
    apply Subtype.ext
    change projection g (handleBoundaryPoint 1) = projection g (handleBoundaryPoint 0)
    congr 1
    apply Subtype.ext
    simp [handleBoundaryPoint]

/-- Every vertex of the actual `4g`-gon is the same point in the quotient. -/
theorem clockVertex_eq_base {g : ℕ} (hg : 0 < g) (k : Fin (4 * g + 1)) :
    projection g (handleBoundaryPoint (k.val / (4 * (g : ℝ)))) = (boundaryBase g).val := by
  by_cases hk : k.val < 4 * g
  · let i : Fin g := ⟨k.val / 4, by omega⟩
    let j : Fin 5 := ⟨k.val % 4, by omega⟩
    have hn : k.val = 4 * (k.val / 4) + k.val % 4 := by omega
    have he : (k.val : ℝ) = 4 * (i.val : ℝ) + (j.val : ℝ) := by
      dsimp [i, j]
      exact_mod_cast hn
    change canonicalHandleVertex g (k.val : ℝ) = (boundaryBase g).val
    rw [he]
    exact (HandleSeparation.blockVertex_quotient_zero i j).trans
      (by simp [canonicalHandleVertex, boundaryBase, projection])
  · have hk' : k.val = 4 * g := by omega
    have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
    have hn : (k.val : ℝ) = 4 * (g : ℝ) := by exact_mod_cast hk'
    rw [hn, div_self (mul_ne_zero (by norm_num) hg')]
    change projection g (handleBoundaryPoint 1) = projection g (handleBoundaryPoint 0)
    congr 1
    apply Subtype.ext
    simp [handleBoundaryPoint]

/-- Equal-time subdivision at the actual polygon vertices. -/
def boundaryTime {g : ℕ} (hg : 0 < g) (k : Fin (4 * g + 1)) : unitInterval :=
  ⟨k.val / (4 * (g : ℝ)), by
    have hden : 0 < 4 * (g : ℝ) := by positivity
    refine ⟨div_nonneg (Nat.cast_nonneg _) hden.le, (div_le_one hden).mpr ?_⟩
    have hk : k.val ≤ 4 * g := by omega
    exact_mod_cast hk⟩

@[simp] theorem boundaryTime_zero {g : ℕ} (hg : 0 < g) : boundaryTime hg 0 = 0 := by
  apply Subtype.ext
  simp [boundaryTime]

@[simp] theorem boundaryTime_last {g : ℕ} (hg : 0 < g) :
    boundaryTime hg (Fin.last (4 * g)) = 1 := by
  apply Subtype.ext
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  change ((4 * g : ℕ) : ℝ) / (4 * (g : ℝ)) = 1
  have hn : ((4 * g : ℕ) : ℝ) = 4 * (g : ℝ) := by norm_num
  rw [hn]
  exact div_self (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hg')

theorem boundaryLoop_time {g : ℕ} (hg : 0 < g) (k : Fin (4 * g + 1)) :
    boundaryLoop g (boundaryTime hg k) = boundaryBase g := by
  apply Subtype.ext
  exact clockVertex_eq_base hg k

/-- The actual loop along any one of the four sides of a handle block. -/
def sideLoop {g : ℕ} (d : HandleSeparation.Side g) :
    Path (boundaryBase g) (boundaryBase g) where
  toFun t := ⟨projection g (HandleSeparation.sidePoint d t),
    ⟨_, HandleCW.sidePoint_norm_one _ _, rfl⟩⟩
  continuous_toFun := ((projection_continuous g).comp
    (HandleSeparation.sidePoint_continuous d)).subtype_mk _
  source' := by
    apply Subtype.ext
    exact (HandleSeparation.sidePoint_endpoint_quotient_zero d 0 (Or.inl rfl)).trans
      (by simp [canonicalHandleVertex, boundaryBase, projection])
  target' := by
    apply Subtype.ext
    exact (HandleSeparation.sidePoint_endpoint_quotient_zero d 1 (Or.inr rfl)).trans
      (by simp [canonicalHandleVertex, boundaryBase, projection])

/-- The index of the literal chronological side, with four consecutive sides per handle. -/
def sideIndex {g : ℕ} (k : Fin (4 * g)) : HandleSeparation.Side g :=
  (⟨k.val / 4, by have hk := k.isLt; omega⟩, ⟨k.val % 4, by omega⟩)

private theorem sideIndex_block {g : ℕ} (i : Fin g) (j : Fin 4) :
    sideIndex (g := g) ⟨4 * i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩ =
      (i, j) := by
  apply Prod.ext <;> apply Fin.ext <;> dsimp [sideIndex] <;> omega

/-- Each true polygon subpath is exactly the corresponding literal side loop. -/
private theorem boundarySubpath_eq_sideLoop {g : ℕ} (hg : 0 < g) (k : Fin (4 * g)) :
    basedSubpath (boundaryLoop g) (boundaryTime hg k.castSucc) (boundaryTime hg k.succ)
      (boundaryLoop_time hg k.castSucc) (boundaryLoop_time hg k.succ) = sideLoop (sideIndex k) := by
  apply Path.ext
  funext s
  apply Subtype.ext
  change projection g (handleBoundaryPoint
    ((1 - s.val) * (k.val / (4 * (g : ℝ))) +
      s.val * (((k.val + 1 : ℕ) : ℝ) / (4 * (g : ℝ))))) =
    projection g (handleBoundaryPoint
      ((((HandleSeparation.sideClock (sideIndex k) : ℕ) : ℝ) + s.val) / (4 * (g : ℝ))))
  have hn : HandleSeparation.sideClock (sideIndex k) = k.val := by
    dsimp [HandleSeparation.sideClock, sideIndex]
    omega
  rw [hn]
  push_cast
  congr 2
  ring

/-- The two oppositely oriented a-sides become reverse paths in the actual quotient. -/
theorem sideLoop_a_reverse {g : ℕ} (i : Fin g) :
    sideLoop (i, (2 : Fin 4)) = (sideLoop (i, (0 : Fin 4))).symm := by
  apply Path.ext
  funext t
  apply Subtype.ext
  have h := HandleSeparation.sideRelated_quotient_eq (g := g)
    ⟨(i, (0 : Fin 4)), unitInterval.symm t, rfl, rfl⟩
  simpa [HandleSeparation.mate, unitInterval.symm_symm, sideLoop,
    projection, PolygonQuotient] using h.symm

/-- The two oppositely oriented b-sides become reverse paths in the actual quotient. -/
theorem sideLoop_b_reverse {g : ℕ} (i : Fin g) :
    sideLoop (i, (3 : Fin 4)) = (sideLoop (i, (1 : Fin 4))).symm := by
  apply Path.ext
  funext t
  apply Subtype.ext
  have h := HandleSeparation.sideRelated_quotient_eq (g := g)
    ⟨(i, (1 : Fin 4)), unitInterval.symm t, rfl, rfl⟩
  simpa [HandleSeparation.mate, unitInterval.symm_symm, sideLoop,
    projection, PolygonQuotient] using h.symm

/-- The inverse boundary class is the chronological product of the inverse side classes. -/
theorem inverse_boundaryLoop_eq_side_product {g : ℕ} (hg : 0 < g) :
    (pathClass (boundaryLoop g))⁻¹ =
      (List.ofFn fun k : Fin (4 * g) => (pathClass (sideLoop (sideIndex k)))⁻¹).prod := by
  have h := inverse_subdivision (boundaryLoop g) (boundaryTime hg) (boundaryLoop_time hg)
  simp_rw [boundarySubpath_eq_sideLoop hg] at h
  have hfull : basedSubpath (boundaryLoop g) (boundaryTime hg 0)
      (boundaryTime hg (Fin.last (4 * g))) (boundaryLoop_time hg 0)
      (boundaryLoop_time hg (Fin.last (4 * g))) = boundaryLoop g := by
    ext s
    simp [basedSubpath, Path.subpath]
  rw [hfull] at h
  exact h.symm

/-- The actual attaching circle gives the standard product of commutators of the inverse
positive edge loops. The inverse accounts for Mathlib's endomorphism-group multiplication. -/
theorem inverse_boundaryLoop_eq_commutator_product {g : ℕ} (hg : 0 < g) :
    (pathClass (boundaryLoop g))⁻¹ =
      (List.ofFn fun i : Fin g =>
        (pathClass (sideLoop (i, (0 : Fin 4))))⁻¹ *
        (pathClass (sideLoop (i, (1 : Fin 4))))⁻¹ *
        pathClass (sideLoop (i, (0 : Fin 4))) *
        pathClass (sideLoop (i, (1 : Fin 4)))).prod := by
  rw [inverse_boundaryLoop_eq_side_product hg, List.ofFn_mul', List.prod_flatten]
  simp only [List.map_ofFn, sideIndex_block]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ, sideLoop_a_reverse, sideLoop_b_reverse, mul_assoc]

/-- The positive side loop is the image of the once-around circle loop under its actual
geometric side map. -/
theorem sideLoop_positive_class {g : ℕ} (d : Edge g) :
    pathClass (sideLoop (HandleCW.edgeSide d)) =
      FundamentalGroup.mapOfEq (circleEdge d) (circleEdge_one d) (pathClass Circle.expLoop) := by
  have hp : sideLoop (HandleCW.edgeSide d) =
      ((Circle.expLoop.map (circleEdge d).continuous).cast
        (circleEdge_one d).symm (circleEdge_one d).symm) := by
    apply Path.ext
    funext t
    have hc : Circle.expLoop t = circleParameter t := by
      simp [Circle.expLoop_apply, circleParameter, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, div_one]
    change _ = circleEdge d (Circle.expLoop t)
    rw [hc, circleEdge_parameter]
    rfl
  rw [hp]
  simp only [pathClass, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]

/-- The free basis furnished by the actual boundary homeomorphism consists exactly of the
actual positive polygon-edge loops. -/
theorem boundaryFundamentalGroupMulEquiv_sideLoop (g : ℕ) (hg : 0 < g) (d : Edge g) :
    boundaryFundamentalGroupMulEquiv g hg (pathClass (sideLoop (HandleCW.edgeSide d))) =
      FreeGroup.of d := by
  let e := bouquetHomeomorphBoundary g hg
  let E := TauCeti.FundamentalGroup.homeomorphMulEquivOfEq e
    (bouquetHomeomorphBoundary_base g hg)
  let p := pathClass Circle.expLoop
  let q := FundamentalGroup.mapOfEq (TauCeti.WedgeSum.incl (fun _ : Edge g => (1 : Circle)) d)
    (TauCeti.WedgeSum.incl_apply_self d) p
  have hm : (⟨e, e.continuous⟩ : C(BoundaryBouquet g, Boundary g)).comp
      (TauCeti.WedgeSum.incl (fun _ : Edge g => (1 : Circle)) d) = circleEdge d := by
    exact ContinuousMap.ext (bouquetHomeomorphBoundary_incl g hg d)
  have hEq : E q = pathClass (sideLoop (HandleCW.edgeSide d)) := by
    rw [sideLoop_positive_class]
    change FundamentalGroup.mapOfEq ⟨e, e.continuous⟩
      (bouquetHomeomorphBoundary_base g hg)
      (FundamentalGroup.mapOfEq (TauCeti.WedgeSum.incl (fun _ : Edge g => (1 : Circle)) d)
        (TauCeti.WedgeSum.incl_apply_self d) p) = _
    rw [TauCeti.FundamentalGroup.mapOfEq_comp]
    exact TauCeti.FundamentalGroup.mapOfEq_congr hm _ _ p
  change TauCeti.WedgeSum.circleFundamentalGroupMulEquiv (Edge g)
    (E.symm (pathClass (sideLoop (HandleCW.edgeSide d)))) = FreeGroup.of d
  rw [← hEq, E.symm_apply_apply]
  exact TauCeti.WedgeSum.circleFundamentalGroupMulEquiv_expLoop d

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
