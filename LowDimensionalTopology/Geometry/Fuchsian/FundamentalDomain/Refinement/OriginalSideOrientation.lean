/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalRefinedSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalCompactSideBoundary
public import LowDimensionalTopology.Geometry.Polygon.Support.ConvexDiscPolygonSupports
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.Moise.PolygonalJordan
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-! Original determinant, convex support and boundary-traversal proofs for the actual original side pairing. Finite and ideal endpoints are treated in the same closed Klein model. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open scoped ComplexConjugate Complex.UnitDisc OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation

def homogeneous (z : ℂ) : Fin 3 → ℝ :=
  ![1 + Complex.normSq z, 2*z.re, 2*z.im]

def discMatrix (a c : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Complex.normSq a + Complex.normSq c,
      2*(a*conj c).re, 2*(a*conj c).im;
     2*(a*c).re, (a^2+(conj c)^2).re, (a^2+(conj c)^2).im;
     -2*(a*c).im, -(a^2-(conj c)^2).im, (a^2-(conj c)^2).re]

theorem discMatrix_det (a c : ℂ) :
    (discMatrix a c).det = (Complex.normSq a-Complex.normSq c)^3 := by
  simp [discMatrix,Matrix.det_fin_three,Complex.normSq_apply,Complex.mul_re,
    Complex.mul_im,pow_two]
  ring

theorem homogeneous_numerator (a c z : ℂ) :
    ![Complex.normSq (a*z+conj c)+Complex.normSq (c*z+conj a),
      2*((a*z+conj c)*conj (c*z+conj a)).re,
      2*((a*z+conj c)*conj (c*z+conj a)).im] =
      homogeneous z ᵥ* discMatrix a c := by
  ext i
  fin_cases i <;>
    simp [homogeneous,discMatrix,Matrix.vecMul,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im,pow_two] <;> ring

theorem homogeneous_div (u v : ℂ) (hv : v ≠ 0) :
    Complex.normSq v • homogeneous (u/v) =
      ![Complex.normSq u+Complex.normSq v,
        2*(u*conj v).re,2*(u*conj v).im] := by
  have hv' : Complex.normSq v ≠ 0 := (Complex.normSq_pos.mpr hv).ne'
  ext i
  fin_cases i <;>
    simp [homogeneous,Complex.div_re,Complex.div_im,
      Complex.mul_re,Complex.mul_im] <;> field_simp [hv'] <;> ring

def rows (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i => homogeneous (z i)

theorem homogeneous_fractional (a c z : ℂ) (hden : c*z+conj a ≠ 0) :
    Complex.normSq (c*z+conj
      a) • homogeneous (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z) =
      homogeneous z ᵥ* discMatrix a c := by
  change Complex.normSq (c*z+conj a) • homogeneous ((a*z+conj c)/(c*z+conj a)) = _
  rw [homogeneous_div _ _ hden,homogeneous_numerator]

theorem rows_fractional (a c : ℂ) (z : Fin 3 → ℂ)
    (hden : ∀i,c*z i+conj a ≠ 0) :
    Matrix.of (fun i j => Complex.normSq (c*z i+conj a) *
      rows (fun i => _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z i)) i j) =
      rows z * discMatrix a c := by
  ext i j
  exact congrFun (homogeneous_fractional a c (z i) (hden i)) j

theorem rows_fractional_det (a c : ℂ) (z : Fin 3 → ℂ)
    (hdet : Complex.normSq a-Complex.normSq c=1)
    (hden : ∀i,c*z i+conj a ≠ 0) :
    (∏i,Complex.normSq (c*z i+conj a)) *
      (rows (fun i => _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z i))).det = (rows z).det := by
  have h := congrArg Matrix.det (rows_fractional a c z hden)
  rw [Matrix.det_mul_column,Matrix.det_mul,discMatrix_det,hdet,one_pow,mul_one] at h
  exact h

def signedArea (p q r : ℂ) : ℝ := (conj (q-p)*(r-p)).im

theorem homogeneous_klein_scaled (z : ℂ) :
    homogeneous z = (1+Complex.normSq z) • ![1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z).re,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z).im] := by
  have hn : 1+Complex.normSq z ≠ 0 := ne_of_gt (by linarith [Complex.normSq_nonneg z])
  have hnorm : ‖z‖^2=Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
  have hre : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z).re=2*z.re/(1+Complex.normSq z) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,hnorm,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    ring
  have him : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z).im=2*z.im/(1+Complex.normSq z) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,hnorm,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero]
    ring
  ext i
  fin_cases i <;> simp [homogeneous,hre,him] <;> field_simp [hn]

theorem rows_det_klein (z : Fin 3 → ℂ) :
    (rows z).det = (∏i : Fin 3, (1+Complex.normSq (z i))) *
      signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 0)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 2)) := by
  have hr : rows z = Matrix.of (fun i j => (1+Complex.normSq (z i)) *
      (![1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z i)).re,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z i)).im] j)) := by
    ext i j
    exact congrFun (homogeneous_klein_scaled (z i)) j
  rw [hr,Matrix.det_mul_column (fun i : Fin 3 => 1+Complex.normSq (z i))
    (fun i => ![1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z
      i)).re,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z i)).im])]
  congr 1
  rw [Matrix.det_fin_three]
  simp [signedArea,Complex.mul_im]
  ring

theorem rows_det_pos_iff (z : Fin 3 → ℂ) :
    0 < (rows z).det ↔
      0 < signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 0)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 2)) := by
  rw [rows_det_klein]
  exact mul_pos_iff_of_pos_left (Finset.prod_pos fun i _ => by linarith [Complex.normSq_nonneg (z i)])

theorem fractional_klein_signedArea_pos_iff (a c p q r : ℂ)
    (hdet : Complex.normSq a-Complex.normSq c=1)
    (hp : c*p+conj a≠0) (hq : c*q+conj a≠0) (hr : c*r+conj a≠0) :
    0 < signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c p))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
        (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c q))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
        (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c r)) ↔
    0 < signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula q) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula r) := by
  let z : Fin 3 → ℂ := ![p,q,r]
  have hd : ∀i,c*z i+conj a≠0 := by intro i;fin_cases i <;> assumption
  have h := rows_fractional_det a c z hdet hd
  have hprod : 0 < ∏i,Complex.normSq (c*z i+conj a) :=
    Finset.prod_pos fun i _ => Complex.normSq_pos.mpr (hd i)
  change (0 < signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z 0)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z 1)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z 2)))) ↔
      0 < signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z
        0)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z
        1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z 2))
  rw [←rows_det_pos_iff (fun i => _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c (z
    i)),
    ←rows_det_pos_iff z,←h]
  exact (mul_pos_iff_of_pos_left hprod).symm

theorem signedArea_inner (p q x : ℂ) :
    signedArea p q x=inner ℝ (Complex.I*(q-p)) x-inner ℝ (Complex.I*(q-p)) p := by
  simp [signedArea,Complex.inner,Complex.mul_re,Complex.mul_im]
  ring

theorem signedArea_swap (p q r : ℂ) : signedArea q p r = -signedArea p q r := by
  simp [signedArea,Complex.mul_im]
  ring

theorem opposite_convex_signedArea {U V : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty)
    (hd : Disjoint U V) {p q u v : ℂ} (hpq : p≠q)
    (hp : p∈closure U∩closure V) (hq : q∈closure U∩closure V)
    (hu : u∈U) (hv : v∈V) (huSide : 0<signedArea p q u) :
    signedArea p q v<0 := by
  obtain ⟨n,t,hn,hU,hV⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator
    hUc hUo hUn hVc hVo hVn hd
  have hnp := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hU hV hp
  have hnq := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hU hV hq
  let m := Complex.I*(q-p)
  have hm : m≠0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr (Ne.symm hpq))
  have hmp : inner ℝ m p=inner ℝ m p := rfl
  have hmq : inner ℝ m q=inner ℝ m p := by
    have h := signedArea_inner p q q
    have hzero : signedArea p q q=0 := by simp [signedArea,Complex.mul_im];ring
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  have hcross := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_difference_cross (x:=v) (u:=u)
    hn hm hpq hnp hnq hmp hmq
  have hneg : inner ℝ n u-t<0 := sub_neg.mpr (hU u hu)
  have hpos : 0 < inner ℝ n v-t := sub_pos.mpr (hV v hv)
  have hmu : 0 < inner ℝ m u-inner ℝ m p := by rw [←signedArea_inner];exact huSide
  have hproduct : 0<(inner ℝ m v-inner ℝ m p)*(inner ℝ n u-t) := by
    rw [hcross]
    exact mul_pos hpos hmu
  rw [signedArea_inner]
  rcases mul_pos_iff.mp hproduct with h|h
  · exact False.elim (hneg.not_gt h.2)
  · exact h.1

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace in
theorem compactified_signedArea_pos_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) (g : H) (p q r : 𝕔𝔻) :
    0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((P.compactifiedAction
      g).closedMap p))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((P.compactifiedAction g).closedMap q))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((P.compactifiedAction g).closedMap r)) ↔
    0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate r) := by
  obtain ⟨a,c,hdet,hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val (P.image_eq g)
  have hc (z : 𝕔𝔻) : ((P.compactifiedAction g).closedMap z : ℂ)=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z := by
    have h := P.compactifiedAction_sphere g z
    change ((((P.compactifiedAction g).closedMap z : 𝕔𝔻) : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (g.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ((z : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at h
    rw [hform,_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c z hdet
      z.norm_le_one] at h
    exact OnePoint.coe_injective h
  change 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
    _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
    _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula _) ↔
    0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula _)
  rw [hc p,hc q,hc r]
  exact fractional_klein_signedArea_pos_iff a c p q r hdet
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet p.norm_le_one)
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet q.norm_le_one)
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet r.norm_le_one)

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace in
theorem original_side_endpoint_closures {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D) (s :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianPolygonSides P D)
    (p : 𝕔𝔻) (hp : p∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel s) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈closure (P.kleinCoordinate '' D) ∩
      closure (P.kleinCoordinate '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD s • D)) := by
  have hpc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈closure (P.kleinCoordinate '' s.val) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel_klein_image]
    exact mem_image_of_mem _ hp
  have hsub : P.kleinCoordinate '' s.val⊆closure (P.kleinCoordinate '' D) ∩
      closure (P.kleinCoordinate '' (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD s • D)) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [(_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement_spec hD s).2] at hx
    exact ⟨image_closure_subset_closure_image P.kleinCoordinate_isOpenEmbedding.continuous
      (mem_image_of_mem _ hx.1),P.klein_closed_tile_subset_closure D _ (mem_image_of_mem _ hx.2)⟩
  exact closure_minimal hsub (isClosed_closure.inter isClosed_closure) hpc

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace in
theorem original_side_opposite_signedArea {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D) (s :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianPolygonSides P D)
    (p q : 𝕔𝔻) (hpq : p≠q) (hp : p∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel s)
    (hq : q∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel s) (u v : P.domain.carrier)
    (hu : u∈D) (hv : v∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD s • D)
    (huSide : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate u)) :
    signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate v)<0 := by
  have hDo := ((_root_.LowDimensionalTopology.Geometry.Fuchsian.isFuchsianFundamentalDomain_iff P D).mp
    hD.locallyFinite.fundamental).1
  have hDn := ((_root_.LowDimensionalTopology.Geometry.Fuchsian.isFuchsianFundamentalDomain_iff P D).mp
    hD.locallyFinite.fundamental).2.1.nonempty
  let g := _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD s
  have hg : g≠1 := (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement_spec hD s).1
  have hd : Disjoint (P.kleinCoordinate '' D) (P.kleinCoordinate '' (g • D)) := by
    simpa only [one_smul] using hD.locallyFinite.fundamental.klein_images_disjoint (Ne.symm hg)
  exact opposite_convex_signedArea hD.klein_convex
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap D hDo) (hDn.image P.kleinCoordinate)
    (hD.klein_smul_convex g)
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap (g • D) ((Homeomorph.smul g).isOpenMap D hDo))
    ((hDn.image (fun x => g•x)).image P.kleinCoordinate) hd
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq)
    (original_side_endpoint_closures hD s p hp) (original_side_endpoint_closures hD s q hq)
    (mem_image_of_mem _ hu) (mem_image_of_mem _ hv) huSide

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace in
theorem original_refined_pairing_reverse_of_positive {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D) (v :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide hD)
    (p q a b : 𝕔𝔻) (hpq : p≠q) (hab : a≠b)
    (hs : v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (ht : v.pair.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b)
    (o : P.domain.carrier) (ho : o∈D)
    (hleft : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate o))
    (hleft' : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b) (P.kleinCoordinate o)) :
    (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD
      v.val.1)⁻¹).closedMap p=b ∧
      (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD v.val.1)⁻¹).closedMap q=a := by
  let g := (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD v.val.1)⁻¹
  let f := (P.compactifiedAction g).closedMap
  have he : ({f p,f q} : Set 𝕔𝔻)={a,b} := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.closed_segment_image_endpoints
    rw [←hs,←ht]
    exact v.pair_carrier
  have hpa : a∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel v.pair.val.1 :=
    v.pair.carrier_subset_original (ht.symm ▸
      _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem a b)
  have hpb : b∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel v.pair.val.1 :=
    v.pair.carrier_subset_original (ht.symm ▸
      _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_right_mem a b)
  have hgo : g•o∈_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD v.pair.val.1 •D := by
    rw [v.pair_element]
    exact mem_smul_set.mpr ⟨o,ho,rfl⟩
  have hnegative := original_side_opposite_signedArea hD v.pair.val.1 a b hab hpa hpb o (g•o) ho hgo hleft'
  have hpositive := (compactified_signedArea_pos_iff P g p q
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate o))).mpr hleft
  rw [P.compactifiedAction_finite,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at hpositive
  have hpmap : f p=a∨f p=b := by
    have hh : f p∈({a,b} : Set 𝕔𝔻) := he ▸ (by simp)
    simpa only [mem_insert_iff,mem_singleton_iff] using hh
  have hqmap : f q=a∨f q=b := by
    have hh : f q∈({a,b} : Set 𝕔𝔻) := he ▸ (by simp)
    simpa only [mem_insert_iff,mem_singleton_iff] using hh
  change signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (f
    p)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (f q))
    (P.kleinCoordinate (g•o))>0 at hpositive
  rcases hpmap with hp|hp
  · rcases hqmap with hq|hq
    · exact False.elim (hpq (f.injective (hp.trans hq.symm)))
    · rw [hp,hq] at hpositive
      exact False.elim (hnegative.not_gt hpositive)
  · refine ⟨hp,?_⟩
    rcases hqmap with hq|hq
    · exact hq
    · exact False.elim (hpq (f.injective (hp.trans hq.symm)))

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace in
theorem original_refined_pairing_reverse {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D) (v :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide hD)
    (p q a b : 𝕔𝔻) (hpq : p≠q) (hab : a≠b)
    (hs : v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (ht : v.pair.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment a b)
    (o : P.domain.carrier) (ho : o∈D)
    (htraversal : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (P.kleinCoordinate o) *
      signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b) (P.kleinCoordinate o)) :
    (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD
      v.val.1)⁻¹).closedMap p=b ∧
      (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD v.val.1)⁻¹).closedMap q=a := by
  rcases mul_pos_iff.mp htraversal with h|h
  · exact original_refined_pairing_reverse_of_positive hD v p q a b hpq hab hs ht o ho h.1 h.2
  · have hs' : v.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment q p := hs.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm p q)
    have ht' : v.pair.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment b a := ht.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm a b)
    have h1 : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (P.kleinCoordinate o) := by
      rw [signedArea_swap]
      exact neg_pos.mpr h.1
    have h2 : 0<signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate a) (P.kleinCoordinate o) := by
      rw [signedArea_swap]
      exact neg_pos.mpr h.2
    have hh := original_refined_pairing_reverse_of_positive hD v q p b a hpq.symm hab.symm hs' ht' o ho h1 h2
    exact ⟨hh.2,hh.1⟩

end LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation

namespace LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation

theorem boundary_segment_support {U : Set ℂ} (hc : Convex ℝ U) (ho : IsOpen U)
    (hne : U.Nonempty) {p q : ℂ} (hseg : segment ℝ p q⊆frontier U) :
    ∃(n : ℂ)(t : ℝ),n≠0 ∧ (∀x∈U,inner ℝ n x<t) ∧
      inner ℝ n p=t ∧ inner ℝ n q=t ∧ ∀x∈closure U,inner ℝ n x≤t := by
  let z := midpoint ℝ p q
  have hz : z∈frontier U := hseg (midpoint_mem_segment p q)
  have hzu : z∉U := by simpa only [ho.interior_eq] using hz.2
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hc ho hzu
  have hbound : ∀x∈closure U,f x≤f z :=
    closure_minimal (fun x hx => (hf x hx).le) (isClosed_le f.continuous continuous_const)
  have hp := hbound p (hseg (left_mem_segment ℝ p q)).1
  have hq := hbound q (hseg (right_mem_segment ℝ p q)).1
  have hmid : 2*f z=f p+f q := by
    dsimp [z]
    rw [midpoint_eq_smul_add,map_smul,map_add]
    norm_num
    ring
  have hpe : f p=f z := by linarith only [hp,hq,hmid]
  have hqe : f q=f z := by linarith only [hp,hq,hmid]
  let n := _root_.LowDimensionalTopology.Geometry.Polygon.complexLinearFunctionalNormal f.toLinearMap
  have he (x : ℂ) : inner ℝ n x=f x := _root_.LowDimensionalTopology.Geometry.Polygon.complexLinearFunctionalNormal_inner f.toLinearMap x
  have hn : n≠0 := by
    obtain ⟨x,hx⟩ := hne
    have hlt := hf x hx
    intro hn
    rw [←he x,←he z,hn,inner_zero_left,inner_zero_left] at hlt
    exact lt_irrefl _ hlt
  refine ⟨n,f z,hn,?_,?_,?_,?_⟩
  · intro x hx
    rw [he]
    exact hf x hx
  · rw [he]
    exact hpe
  · rw [he]
    exact hqe
  · intro x hx
    rw [he]
    exact hbound x hx

theorem signedArea_support_properties {U : Set ℂ} {p q o n : ℂ} {t : ℝ}
    (hpq : p≠q) (hn : n≠0) (hp : inner ℝ n p=t) (hq : inner ℝ n q=t)
    (ho : inner ℝ n o<t) (hbound : ∀x∈closure U,inner ℝ n x≤t) :
    signedArea p q o≠0 ∧ ∀x∈closure U,0 ≤ signedArea p q o*signedArea p q x := by
  let m := Complex.I*(q-p)
  have hm : m≠0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hpq.symm)
  have hmp : inner ℝ m p=inner ℝ m p := rfl
  have hmq : inner ℝ m q=inner ℝ m p := by
    have h := signedArea_inner p q q
    have hz : signedArea p q q=0 := by simp [signedArea,Complex.mul_im];ring
    rw [hz] at h
    exact sub_eq_zero.mp h.symm
  have hA : signedArea p q o≠0 := by
    intro hzero
    have hmo : inner ℝ m o=inner ℝ m p := by
      have h := signedArea_inner p q o
      rw [hzero] at h
      exact sub_eq_zero.mp h.symm
    have he := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points (x:=o) hn hm hpq hp hq hmp hmq
    exact ho.ne (he.mpr hmo)
  refine ⟨hA,?_⟩
  intro x hx
  have hcross := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_difference_cross (x:=x) (u:=o) hn hm hpq hp hq hmp hmq
  change (inner ℝ m x-inner ℝ m p)*(inner ℝ n o-t)=
    (inner ℝ n x-t)*(inner ℝ m o-inner ℝ m p) at hcross
  rw [←signedArea_inner p q x,←signedArea_inner p q o] at hcross
  have hnu : inner ℝ n o-t<0 := sub_neg.mpr ho
  have hnx : inner ℝ n x-t≤0 := sub_nonpos.mpr (hbound x hx)
  rcases lt_or_gt_of_ne hA with hneg|hpos
  · have hright : 0≤(inner ℝ n x-t)*signedArea p q o := mul_nonneg_of_nonpos_of_nonpos hnx hneg.le
    have hleft : signedArea p q x≤0 := by
      by_contra hh
      have hbad := mul_neg_of_pos_of_neg (lt_of_not_ge hh) hnu
      linarith only [hcross,hright,hbad]
    exact mul_nonneg_of_nonpos_of_nonpos hneg.le hleft
  · have hright : (inner ℝ n x-t)*signedArea p q o≤0 := mul_nonpos_of_nonpos_of_nonneg hnx hpos.le
    have hleft : 0 ≤ signedArea p q x := by
      by_contra hh
      have hbad := mul_pos_of_neg_of_neg (lt_of_not_ge hh) hnu
      linarith only [hcross,hright,hbad]
    exact mul_nonneg hpos.le hleft

theorem boundary_segment_signedArea {U : Set ℂ} (hc : Convex ℝ U) (ho : IsOpen U)
    {p q o : ℂ} (hpq : p≠q) (hseg : segment ℝ p q⊆frontier U) (hoU : o∈U) :
    signedArea p q o≠0 ∧ ∀x∈closure U,0 ≤ signedArea p q o*signedArea p q x := by
  obtain ⟨n,t,hn,hlt,hp,hq,hbound⟩ := boundary_segment_support hc ho ⟨o,hoU⟩ hseg
  exact signedArea_support_properties hpq hn hp hq (hlt o hoU) hbound

theorem signedArea_rotate (p q r : ℂ) : signedArea q r p=signedArea p q r := by
  simp [signedArea,Complex.mul_im]
  ring

theorem signedArea_zero_collinear {p q r : ℂ} (hpq : p≠q)
    (hzero : signedArea p q r=0) : Collinear ℝ ({p,q,r} : Set ℂ) := by
  let m := Complex.I*(q-p)
  have hm : m≠0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hpq.symm)
  apply _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplex_hyperplane_collinear m p hm (by simp)
  intro x hx
  have hz : signedArea p q x=0 := by
    rcases hx with hx|hx|hx
    · rw [hx]
      simp [signedArea]
    · rw [hx]
      simp [signedArea,Complex.mul_im]
      ring
    · rw [hx]
      exact hzero
  rw [signedArea_inner] at hz
  exact sub_eq_zero.mp hz

theorem collinear_consecutive_sbtw {p q r : ℂ} (hpq : p≠q) (hqr : q≠r)
    (hc : Collinear ℝ ({p,q,r} : Set ℂ))
    (hinter : segment ℝ p q∩segment ℝ q r={q}) : Sbtw ℝ p q r := by
  rcases hc.wbtw_or_wbtw_or_wbtw with h|h|h
  · exact ⟨h,hpq.symm,hqr⟩
  · have hr : r∈segment ℝ p q := by rw [segment_symm];exact h.mem_segment
    have he : r=q := by
      have hh : r∈segment ℝ p q∩segment ℝ q r := ⟨hr,right_mem_segment ℝ q r⟩
      rw [hinter] at hh
      exact hh
    exact False.elim (hqr he.symm)
  · have hp : p∈segment ℝ q r := by rw [segment_symm];exact h.mem_segment
    have he : p=q := by
      have hh : p∈segment ℝ p q∩segment ℝ q r := ⟨left_mem_segment ℝ p q,hp⟩
      rw [hinter] at hh
      exact hh
    exact False.elim (hpq he)

theorem signedArea_lineMap (p q o : ℂ) (t : ℝ) :
    signedArea q (AffineMap.lineMap p q t) o=(t-1)*signedArea p q o := by
  simp [signedArea,AffineMap.lineMap_apply_module,Complex.mul_im]
  ring

theorem signedArea_sbtw_mul_pos {p q r o : ℂ} (h : Sbtw ℝ p q r)
    (hne : signedArea p q o≠0) : 0<signedArea p q o*signedArea q r o := by
  obtain ⟨t,ht,rfl⟩ := h.right_mem_image_Ioi
  rw [signedArea_lineMap]
  have hh := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hne)
  nlinarith only [hh]

theorem signed_product_trans {a b c : ℝ} (hab : 0<a*b) (hbc : 0<b*c) : 0<a*c := by
  have hb : b≠0 := by intro hb;rw [hb,mul_zero] at hab;exact lt_irrefl _ hab
  have h : 0<(a*c)*b^2 := by
    have hh := mul_pos hab hbc
    nlinarith only [hh]
  exact (mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hb)).mp h

theorem adjacent_signedArea_mul_pos {p q r o : ℂ} (hpq : p≠q) (hqr : q≠r)
    (hinter : segment ℝ p q∩segment ℝ q r={q})
    (ha : signedArea p q o≠0) (hb : signedArea q r o≠0)
    (h1 : 0 ≤ signedArea p q o*signedArea p q r)
    (h2 : 0 ≤ signedArea q r o*signedArea q r p) :
    0<signedArea p q o*signedArea q r o := by
  by_cases hz : signedArea p q r=0
  · exact signedArea_sbtw_mul_pos (collinear_consecutive_sbtw hpq hqr
      (signedArea_zero_collinear hpq hz) hinter) ha
  · rw [signedArea_rotate p q r] at h2
    have h1' : 0<signedArea p q o*signedArea p q r :=
      lt_of_le_of_ne h1 (Ne.symm (mul_ne_zero ha hz))
    have h2' : 0<signedArea q r o*signedArea p q r :=
      lt_of_le_of_ne h2 (Ne.symm (mul_ne_zero hb hz))
    exact signed_product_trans h1' (by simpa only [mul_comm] using h2')

theorem convex_cyclic_traversal_signedArea {n : ℕ} [NeZero n]
    {U : Set ℂ} (hc : Convex ℝ U) (ho : IsOpen U)
    (z : ZMod n→ℂ) (hadj : ∀i,z i≠z (i+1))
    (hinter : ∀i,segment ℝ (z i) (z (i+1))∩segment ℝ (z (i+1)) (z ((i+1)+1))={z (i+1)})
    (hseg : ∀i,segment ℝ (z i) (z (i+1))⊆frontier U)
    (o : ℂ) (hoU : o∈U) :
    ∀i j,0<signedArea (z i) (z (i+1)) o*signedArea (z j) (z (j+1)) o := by
  let A : ZMod n→ℝ := fun i => signedArea (z i) (z (i+1)) o
  have hprops (i : ZMod n) := boundary_segment_signedArea hc ho (hadj i) (hseg i) hoU
  have hnext (i : ZMod n) : 0<A i*A (i+1) := by
    apply adjacent_signedArea_mul_pos (hadj i) (hadj (i+1)) (hinter i) (hprops i).1 (hprops (i+1)).1
    · exact (hprops i).2 _ ((hseg (i+1)) (right_mem_segment ℝ _ _)).1
    · exact (hprops (i+1)).2 _ ((hseg i) (left_mem_segment ℝ _ _)).1
  have hnat (k : ℕ) : 0<A 0*A (k : ZMod n) := by
    induction k with
    | zero =>
      simpa only [Nat.cast_zero,←pow_two] using sq_pos_of_ne_zero (hprops 0).1
    | succ k ih =>
      simpa only [Nat.cast_succ] using signed_product_trans ih (hnext (k : ZMod n))
  have hzero (i : ZMod n) : 0<A 0*A i := by
    simpa only [ZMod.natCast_zmod_val] using hnat i.val
  intro i j
  exact signed_product_trans (by simpa only [mul_comm] using hzero i) (hzero j)

open LeanEval.Topology.ClassificationOfSurfaces.Moise in
theorem polygonalCircle_convex_signedArea (J : PolygonalCircle)
    {U : Set ℂ} (hc : Convex ℝ U) (ho : IsOpen U)
    (hcarrier : PolygonalCircle.planeComplexEquiv '' J.carrier=frontier U)
    (o : ℂ) (hoU : o∈U) :
    ∀i j,0<signedArea (PolygonalCircle.planeComplexEquiv (J.vertex i))
      (PolygonalCircle.planeComplexEquiv (J.vertex (i+1))) o *
      signedArea (PolygonalCircle.planeComplexEquiv (J.vertex j))
      (PolygonalCircle.planeComplexEquiv (J.vertex (j+1))) o := by
  let e := PolygonalCircle.planeComplexEquiv
  have hseg (i : ZMod J.n) :
      segment ℝ (e (J.vertex i)) (e (J.vertex (i+1)))=e '' J.edgeSegment i := by
    exact (image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap _ _).symm
  apply convex_cyclic_traversal_signedArea hc ho (fun i => e (J.vertex i))
    (fun i => e.injective.ne (J.adjacent_ne i))
  · intro i
    rw [hseg i,hseg (i+1),←image_inter e.injective]
    have hi : J.edgeSegment i∩J.edgeSegment (i+1)={J.vertex (i+1)} := by
      simpa only [PolygonalCircle.edgeSegment,add_assoc,one_add_one_eq_two] using J.consecutive_inter i
    rw [hi,image_singleton]
  · intro i
    rw [hseg i,←hcarrier]
    exact image_mono (J.edgeSegment_subset_carrier i)
  · exact hoU

end LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation

namespace LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

local instance originalSideOrientationSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance originalSideOrientationSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem original_cyclic_pairing_reverse {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤)
    (J : PolygonalCircle) (e : ZMod J.n≃_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide hD)
    (z : ZMod J.n→𝕔𝔻)
    (hcarrier : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      (⋃v:_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide hD,v.carrier))
    (hvertex : ∀i,_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane (z i)=J.vertex i)
    (hsegment : ∀i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (z i) (z (i+1))=(e
      i).carrier)
    (i : ZMod J.n) :
    let j := e.symm ((e i).pair)
    (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD (e
      i).val.1)⁻¹).closedMap (z i)=z (j+1) ∧
      (P.compactifiedAction (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideElement hD (e i).val.1)⁻¹).closedMap (z (i+1))=z j := by
  let U := P.kleinCoordinate '' D
  let E := PolygonalCircle.planeComplexEquiv
  have hDo := hD.locallyFinite.fundamental.isOpen
  obtain ⟨o,ho⟩ := ((_root_.LowDimensionalTopology.Geometry.Fuchsian.isFuchsianFundamentalDomain_iff P D).mp
    hD.locallyFinite.fundamental).2.1.nonempty
  have hUo : IsOpen U := P.kleinCoordinate_isOpenEmbedding.isOpenMap D hDo
  have hUn : U.Nonempty := ⟨P.kleinCoordinate o,mem_image_of_mem _ ho⟩
  have hfrontier : frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianPolygonCompactKlein P D)=frontier U := by
    change frontier (closure U)=frontier U
    rw [frontier,frontier,closure_closure,
      hD.klein_convex.interior_closure_eq_interior_of_nonempty_interior
        (hUo.interior_eq.symm ▸ hUn)]
  have hJ : E '' J.carrier=frontier U := by
    rw [hcarrier,image_image]
    have he : (fun p : 𝕔𝔻 => E (_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane p))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate := by
      funext p
      exact E.apply_symm_apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
    rw [he,_root_.LowDimensionalTopology.Geometry.Fuchsian.originalRefinedSide_iUnion_carrier,image_iUnion]
    simp_rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianSideClosedModel_klein_image]
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.finite_area_original_compact_boundary hD ha,hfrontier]
  have hz (k : ZMod J.n) : E (J.vertex k)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (z k) := by
    rw [←hvertex k]
    exact E.apply_symm_apply _
  have hsame := polygonalCircle_convex_signedArea J hD.klein_convex hUo hJ
    (P.kleinCoordinate o) (mem_image_of_mem _ ho)
  let j := e.symm ((e i).pair)
  have hej : e j=(e i).pair := e.apply_symm_apply _
  have hpq (k : ZMod J.n) : z k≠z (k+1) := by
    intro he
    apply J.adjacent_ne k
    rw [←hvertex k,←hvertex (k+1),he]
  have ht : (e i).pair.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (z j) (z (j+1)) := by
    rw [←hej]
    exact (hsegment j).symm
  have htraversal := hsame i j
  rw [hz i,hz (i+1),hz j,hz (j+1)] at htraversal
  exact original_refined_pairing_reverse hD (e i) (z i) (z (i+1)) (z j) (z (j+1))
    (hpq i) (hpq j) (hsegment i).symm ht o ho htraversal

end LowDimensionalTopology.Geometry.Fuchsian.OriginalOrientation
