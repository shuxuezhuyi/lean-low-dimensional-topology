/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaNormalized
@[expose] public section
open Set
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The exact real polynomial obtained from a genuine Klein cut by actual Cayley coordinates. -/
def nielsenHalfPlaneCutPolynomial (n : ℂ) (t x y : ℝ) : ℝ:=
  (t-n.re)*(x^2+y^2)+2*n.im*x+t+n.re

theorem nielsen_halfPlane_klein_cut_iff (n : ℂ) (t : ℝ) (z : ℍ) :
    inner ℝ n (halfPlaneKleinCoordinate z)<t ↔ 0<nielsenHalfPlaneCutPolynomial n t z.re z.im := by
  have hD : 0<z.re^2+z.im^2+1:=by positivity
  have he : inner ℝ n (halfPlaneKleinCoordinate z)=
      (n.re*(z.re^2+z.im^2-1)-2*n.im*z.re)/(z.re^2+z.im^2+1):=by
    rw [halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    ring
  rw [he,div_lt_iff₀ hD]
  unfold nielsenHalfPlaneCutPolynomial
  constructor <;> intro h <;> nlinarith

theorem nielsen_cayley_real_formula (x : ℝ) : cayleyFormula (x : ℂ)=
    ⟨(x^2-1)/(x^2+1),-2*x/(x^2+1)⟩ := by
  apply Complex.ext <;>
    simp [cayleyFormula,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> ring

theorem nielsen_cayley_real_inner (n : ℂ) (x : ℝ) : inner ℝ n (cayleyFormula (x : ℂ))=
    (n.re*(x^2-1)-2*n.im*x)/(x^2+1) := by
  rw [nielsen_cayley_real_formula,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  ring

theorem nielsen_cayley_real_support_iff (n : ℂ) (t x : ℝ) :
    inner ℝ n (cayleyFormula (x : ℂ))≤t ↔ 0≤nielsenHalfPlaneCutPolynomial n t x 0 := by
  rw [nielsen_cayley_real_inner,div_le_iff₀ (by positivity : 0<x^2+1)]
  unfold nielsenHalfPlaneCutPolynomial
  constructor <;> intro h <;> nlinarith

/-- The genuine real complementary-arc forms in a boundary chart with its omitted ideal point in the limit set. -/
inductive NielsenHalfPlaneGap where
  | bounded (a b : ℝ) (hab : a<b)
  | left (b : ℝ)
  | right (a : ℝ)

def NielsenHalfPlaneGap.carrier : NielsenHalfPlaneGap → Set ℝ
  | .bounded a b _=>Ioo a b
  | .left b=>Iio b
  | .right a=>Ioi a

/-- The open hyperbolic side separated from the genuine real arc. -/
def NielsenHalfPlaneGap.keptSide : NielsenHalfPlaneGap → Set ℍ
  | .bounded a b _=>{z | (z.re-a)*(b-z.re)<z.im^2}
  | .left b=>{z | b<z.re}
  | .right a=>{z | z.re<a}

def NielsenHalfPlaneGap.line : NielsenHalfPlaneGap → HalfPlaneLine
  | .bounded a b hab=>.circle ((a+b)/2) ((b-a)/2) (by linarith)
  | .left b=>.vertical b
  | .right a=>.vertical a

/-- The bounded real-arc side is exactly the exterior of its actual semicircle. -/
theorem NielsenHalfPlaneGap.bounded_keptSide (a b : ℝ) (hab : a<b) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).keptSide=
      {z : ℍ | (b-a)/2<‖(z : ℂ)-((a+b)/2 : ℝ)‖} := by
  ext z
  have hnorm : ‖(z : ℂ)-((a+b)/2 : ℝ)‖^2=(z.re-(a+b)/2)^2+z.im^2:=by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  change (z.re-a)*(b-z.re)<z.im^2 ↔ (b-a)/2<‖(z : ℂ)-((a+b)/2 : ℝ)‖
  constructor <;> intro h <;> nlinarith [norm_nonneg ((z : ℂ)-((a+b)/2 : ℝ))]

theorem NielsenHalfPlaneGap.carrier_nonempty (G : NielsenHalfPlaneGap) : G.carrier.Nonempty := by
  cases G with
  | bounded a b hab => exact nonempty_Ioo.mpr hab
  | left b => exact ⟨b-1,by change b-1<b;linarith⟩
  | right a => exact ⟨a+1,by change a<a+1;linarith⟩

theorem NielsenHalfPlaneGap.carrier_isOpen (G : NielsenHalfPlaneGap) : IsOpen G.carrier := by
  cases G with
  | bounded a b hab => exact isOpen_Ioo
  | left b => exact isOpen_Iio
  | right a => exact isOpen_Ioi

theorem NielsenHalfPlaneGap.carrier_preconnected (G : NielsenHalfPlaneGap) : IsPreconnected G.carrier := by
  cases G with
  | bounded a b hab => exact isPreconnected_Ioo
  | left b => exact isPreconnected_Iio
  | right a => exact isPreconnected_Ioi

theorem NielsenHalfPlaneGap.keptSide_eq_openHalfPlane (G : NielsenHalfPlaneGap) (z : ℍ)
    (hz : z∈G.keptSide) : G.keptSide=openHHalfPlane G.line z := by
  cases G with
  | bounded a b hab =>
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.bounded_keptSide a b hab] at hz ⊢
    exact (openHHalfPlane_circle_outside ((a+b)/2) ((b-a)/2) (by linarith) z hz).symm
  | left b => exact (openHHalfPlane_vertical_gt b z hz).symm
  | right a => exact (hReCutLt_eq_openHalfPlane a z hz).symm

/-- Every genuine regular supporting cut whose omitted ideal point is on its retained side
has one of the actual real complementary-arc forms. -/
theorem nielsen_regular_cut_gap (n : ℂ) (t : ℝ) (hcut : |t|<‖n‖) (ha : n.re≤t) :
    ∃G : NielsenHalfPlaneGap,
      (∀z : ℍ,inner ℝ n (halfPlaneKleinCoordinate z)<t ↔ z∈G.keptSide) ∧
      (∀x : ℝ,nielsenHalfPlaneCutPolynomial n t x 0<0 ↔ x∈G.carrier) := by
  have hnorm : ‖n‖^2=n.re^2+n.im^2:=by rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply];ring
  have hdelta : 0<n.re^2+n.im^2-t^2:=by
    nlinarith [sq_abs t,abs_nonneg t,norm_nonneg n]
  by_cases hd : 0<t-n.re
  · let d:=t-n.re
    let δ:=Real.sqrt (n.re^2+n.im^2-t^2)
    let c:= -n.im/d
    let r:=δ/d
    have hd' : 0<d:=hd
    have hδ : 0<δ:=Real.sqrt_pos.2 hdelta
    have hδsq : δ^2=n.re^2+n.im^2-t^2:=Real.sq_sqrt hdelta.le
    have hr : 0<r:=div_pos hδ hd'
    have he (x y : ℝ) : nielsenHalfPlaneCutPolynomial n t x y=
        d*((x-c)^2+y^2-r^2):=by
      dsimp only [c,r]
      simp only [div_pow,hδsq]
      dsimp only [d,nielsenHalfPlaneCutPolynomial]
      field_simp [ne_of_gt hd]
      ring
    refine ⟨.bounded (c-r) (c+r) (by linarith),?_,?_⟩
    · intro z
      rw [nielsen_halfPlane_klein_cut_iff,he,mul_pos_iff_of_pos_left hd']
      change 0<(z.re-c)^2+z.im^2-r^2 ↔ (z.re-(c-r))*(c+r-z.re)<z.im^2
      constructor <;> intro hh <;> nlinarith
    · intro x
      rw [he]
      have hh (q : ℝ) : d*q<0 ↔ q<0:=by constructor <;> intro h <;> nlinarith
      rw [hh]
      change (x-c)^2+0^2-r^2<0 ↔ c-r<x ∧ x<c+r
      constructor
      · intro hh
        constructor <;> nlinarith [sq_nonneg (x-c+r),sq_nonneg (x-c-r)]
      · rintro ⟨hl,hu⟩
        nlinarith [mul_pos (show 0<x-(c-r) by linarith) (show 0<c+r-x by linarith)]
  · have ht : t=n.re:=by linarith
    have hb : n.im≠0:=by intro hh;rw [hh,ht] at hdelta; nlinarith
    let k:= -n.re/n.im
    have he (x y : ℝ) : nielsenHalfPlaneCutPolynomial n t x y=2*n.im*(x-k):=by
      dsimp [nielsenHalfPlaneCutPolynomial,k]
      rw [ht]
      field_simp [hb]
      ring
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · refine ⟨.right k,?_,?_⟩
      · intro z
        rw [nielsen_halfPlane_klein_cut_iff,he]
        change 0<2*n.im*(z.re-k) ↔ z.re<k
        constructor <;> intro hh <;> nlinarith
      · intro x
        rw [he]
        change 2*n.im*(x-k)<0 ↔ k<x
        constructor <;> intro hh <;> nlinarith
    · refine ⟨.left k,?_,?_⟩
      · intro z
        rw [nielsen_halfPlane_klein_cut_iff,he]
        change 0<2*n.im*(z.re-k) ↔ k<z.re
        constructor <;> intro hh <;> nlinarith

      · intro x
        rw [he]
        change 2*n.im*(x-k)<0 ↔ x<k
        constructor <;> intro hh <;> nlinarith

def NielsenHalfPlaneGap.cutNormal : NielsenHalfPlaneGap → ℂ
  | .bounded a b _ => ⟨((((a+b)/2)^2-((b-a)/2)^2)-1)/2,-(a+b)/2⟩
  | .left b => ⟨-b,1⟩
  | .right a => ⟨a,-1⟩

def NielsenHalfPlaneGap.cutThreshold : NielsenHalfPlaneGap → ℝ
  | .bounded a b _ => ((((a+b)/2)^2-((b-a)/2)^2)+1)/2
  | .left b => -b
  | .right a => a

theorem NielsenHalfPlaneGap.cut_regular (G : NielsenHalfPlaneGap) :
    |G.cutThreshold|<‖G.cutNormal‖ ∧ G.cutNormal.re≤G.cutThreshold := by
  have hnorm (n : ℂ) : ‖n‖^2=n.re^2+n.im^2:=by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  constructor
  · apply (sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs,hnorm]
    cases G with
    | bounded a b hab =>
      dsimp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
      nlinarith [sq_pos_of_pos (show 0<b-a by linarith)]
    | left b => dsimp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold];nlinarith
    | right a => dsimp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold];nlinarith
  · cases G <;> dsimp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold] <;> linarith

theorem NielsenHalfPlaneGap.cut_keptSide (G : NielsenHalfPlaneGap) (z : ℍ) :
    inner ℝ G.cutNormal (halfPlaneKleinCoordinate z)<G.cutThreshold ↔ z∈G.keptSide := by
  rw [nielsen_halfPlane_klein_cut_iff]
  cases G with
  | bounded a b hab =>
    change 0<nielsenHalfPlaneCutPolynomial _ _ _ _ ↔ (z.re-a)*(b-z.re)<z.im^2
    dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> nlinarith
  | left b =>
    change 0<nielsenHalfPlaneCutPolynomial _ _ _ _ ↔ b<z.re
    dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> linarith
  | right a =>
    change 0<nielsenHalfPlaneCutPolynomial _ _ _ _ ↔ z.re<a
    dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> linarith

theorem NielsenHalfPlaneGap.cut_carrier (G : NielsenHalfPlaneGap) (x : ℝ) :
    nielsenHalfPlaneCutPolynomial G.cutNormal G.cutThreshold x 0<0 ↔ x∈G.carrier := by
  cases G with
  | bounded a b hab =>
    change nielsenHalfPlaneCutPolynomial _ _ _ _<0 ↔ a<x ∧ x<b
    have he : nielsenHalfPlaneCutPolynomial (_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).cutNormal
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).cutThreshold x 0=(x-a)*(x-b):=by
      dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
      ring
    rw [he]
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (x-a),sq_nonneg (x-b)]
    · rintro ⟨ha,hb⟩
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  | left b =>
    change nielsenHalfPlaneCutPolynomial _ _ _ _<0 ↔ x<b
    dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> linarith

  | right a =>
    change nielsenHalfPlaneCutPolynomial _ _ _ _<0 ↔ a<x
    dsimp [nielsenHalfPlaneCutPolynomial,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> linarith

theorem NielsenHalfPlaneGap.keptSide_antitone (G J : NielsenHalfPlaneGap)
    (h : G.carrier⊆J.carrier) : J.keptSide⊆G.keptSide := by
  cases G with
  | bounded a b hab =>
    cases J with
    | bounded c d hcd =>
      have hh : c≤a ∧ b≤d:=(Ioo_subset_Ioo_iff hab).mp h
      intro z hz
      change (z.re-a)*(b-z.re)<z.im^2
      change (z.re-c)*(d-z.re)<z.im^2 at hz
      by_cases hxa : a<z.re
      · by_cases hxb : z.re<b
        · have hm : (z.re-a)*(b-z.re)≤(z.re-c)*(d-z.re):=
            mul_le_mul (by linarith [hh.1]) (by linarith [hh.2]) (by linarith) (by linarith [hh.1])
          exact hm.trans_lt hz
        · have hm : (z.re-a)*(b-z.re)≤0:=mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          exact hm.trans_lt (sq_pos_of_pos z.im_pos)
      · have hm : (z.re-a)*(b-z.re)≤0:=mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        exact hm.trans_lt (sq_pos_of_pos z.im_pos)
    | left d =>
      have hb : b≤d:=by
        have hh:=closure_mono h (show b∈closure (Ioo a b) by rw [closure_Ioo hab.ne];exact ⟨hab.le,le_refl _⟩)
        simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.carrier,closure_Iio,mem_Iic] using hh
      intro z hz
      change d<z.re at hz
      change (z.re-a)*(b-z.re)<z.im^2
      exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)).trans_lt (sq_pos_of_pos z.im_pos)
    | right c =>
      have ha : c≤a:=by
        have hh:=closure_mono h (show a∈closure (Ioo a b) by rw [closure_Ioo hab.ne];exact ⟨le_refl _,hab.le⟩)
        simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.carrier,closure_Ioi,mem_Ici] using hh
      intro z hz
      change z.re<c at hz
      change (z.re-a)*(b-z.re)<z.im^2
      exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)).trans_lt (sq_pos_of_pos z.im_pos)
  | left b =>
    cases J with
    | bounded c d hcd =>
      have hh:=h (show min b c-1∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.left b).carrier by change min b c-1<b;linarith [min_le_left b c])
      change c<min b c-1 ∧ min b c-1<d at hh
      exact False.elim (by linarith [min_le_right b c])
    | left d =>
      have hb : b≤d:=Iio_subset_Iio_iff.mp h
      intro z hz
      change d<z.re at hz
      change b<z.re
      exact hb.trans_lt hz
    | right c =>
      have hh:=h (show min b c-1∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.left b).carrier by change min b c-1<b;linarith [min_le_left b c])
      change c<min b c-1 at hh
      exact False.elim (by linarith [min_le_right b c])
  | right a =>
    cases J with
    | bounded c d hcd =>
      have hh:=h (show max a d+1∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.right a).carrier by change a<max a d+1;linarith [le_max_left a d])
      change c<max a d+1 ∧ max a d+1<d at hh
      exact False.elim (by linarith [le_max_right a d])
    | left d =>
      have hh:=h (show max a d+1∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.right a).carrier by change a<max a d+1;linarith [le_max_left a d])
      change max a d+1<d at hh
      exact False.elim (by linarith [le_max_right a d])
    | right c =>
      have ha : c≤a:=Ioi_subset_Ioi_iff.mp h
      intro z hz
      change z.re<c at hz
      change z.re<a
      exact hz.trans_le ha

theorem NielsenHalfPlaneGap.keptSide_nonempty (G : NielsenHalfPlaneGap) : G.keptSide.Nonempty := by
  cases G with
  | bounded a b hab =>
    refine ⟨⟨⟨(a+b)/2,b-a+1⟩,by change 0<b-a+1;linarith⟩,?_⟩
    change ((a+b)/2-a)*(b-(a+b)/2)<(b-a+1)^2
    nlinarith [sq_nonneg (b-a)]
  | left b => exact ⟨⟨⟨b+1,1⟩,by norm_num⟩,by change b<b+1;linarith⟩
  | right a => exact ⟨⟨⟨a-1,1⟩,by norm_num⟩,by change a-1<a;linarith⟩

theorem NielsenHalfPlaneGap.keptSide_disjoint_line (G : NielsenHalfPlaneGap) :
    Disjoint G.keptSide G.line.carrier := by
  obtain ⟨z,hz⟩:=G.keptSide_nonempty
  rw [G.keptSide_eq_openHalfPlane z hz]
  exact Set.disjoint_left.mpr (fun _ hu hL=>connectedComponentIn_subset G.line.carrierᶜ z hu hL)

theorem NielsenHalfPlaneGap.idealEndpoints (G : NielsenHalfPlaneGap) :
    G.line.idealEndpoints=match G with
      | .bounded a b _=>{((a : ℂ) : OnePoint ℂ),((b : ℂ) : OnePoint ℂ)}
      | .left b=>{((b : ℂ) : OnePoint ℂ),∞}
      | .right a=>{((a : ℂ) : OnePoint ℂ),∞} := by
  cases G with
  | bounded a b hab =>
    change (HalfPlaneLine.circle _ _ _).idealEndpoints=_
    rw [circle_idealEndpoints]
    have ha : (a+b)/2-(b-a)/2=a:=by ring
    have hb : (a+b)/2+(b-a)/2=b:=by ring
    rw [ha,hb]
  | left b => exact vertical_idealEndpoints b
  | right a => exact vertical_idealEndpoints a

end
end LowDimensionalTopology.Geometry.Hyperbolic
