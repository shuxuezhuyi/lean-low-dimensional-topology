/- An explicit counterexample to compact cofiniteness of arbitrary supporting half-plane families. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Examples.InfiniteSidePolygon
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSupportingHalfPlanes

/-!
# A locally finite polygon with infinitely many essential half-plane cuts

Piecewise linear Klein constraints define a convex region with infinitely many
exposed boundary segments. Reassembling the region inside an explicit discrete
half-plane group gives a locally finite fundamental polygon. Every half-plane
representation must retain infinitely many cuts excluding the same native point.

The slope and seam estimates establish the essential cuts; the window and tile
arguments establish the genuine polygon and local finiteness hypotheses.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology Filter
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def cofiniteCutEpsilon : ℝ:=1/100
def cofiniteCutSeam (n:ℕ) : ℝ:=16*(n:ℝ)^2
def cofiniteCutSlope : ℕ→ℝ
  | 0=>cofiniteCutEpsilon/16
  | n+1=>cofiniteCutEpsilon/(16*((n:ℝ)+1)*(n+2)*(2*n+3))
def cofiniteCutOffset : ℕ→ℝ
  | 0=>-2*cofiniteCutEpsilon
  | n+1=>-cofiniteCutEpsilon/((n:ℝ)+1)-cofiniteCutSeam (n+1)*cofiniteCutSlope (n+1)
def cofiniteCutValue (n:ℕ) (u:ℝ) : ℝ:=cofiniteCutOffset n+cofiniteCutSlope n*u

theorem cofiniteCutSlope_pos (n:ℕ) : 0<cofiniteCutSlope n := by
  cases n <;> dsimp [cofiniteCutSlope,cofiniteCutEpsilon] <;> positivity

theorem cofiniteCutSlope_succ_lt (n:ℕ) : cofiniteCutSlope (n+1)<cofiniteCutSlope n := by
  cases n with
  | zero=>norm_num [cofiniteCutSlope,cofiniteCutEpsilon]
  | succ n=>
    simp only [cofiniteCutSlope,Nat.cast_add,Nat.cast_one]
    apply div_lt_div_of_pos_left (by norm_num [cofiniteCutEpsilon]) (by positivity)
    gcongr <;> norm_num

theorem cofiniteCutSeam_mono : Monotone cofiniteCutSeam := by
  intro n m hnm
  dsimp [cofiniteCutSeam]
  gcongr

theorem cofiniteCutValue_left (n:ℕ) :
    cofiniteCutValue (n+1) (cofiniteCutSeam (n+1))=-cofiniteCutEpsilon/((n:ℝ)+1) := by
  dsimp [cofiniteCutValue,cofiniteCutOffset]
  ring

theorem cofiniteCutValue_right (n:ℕ) :
    cofiniteCutValue n (cofiniteCutSeam (n+1))=-cofiniteCutEpsilon/((n:ℝ)+1) := by
  cases n with
  | zero=>norm_num [cofiniteCutValue,cofiniteCutOffset,cofiniteCutSlope,cofiniteCutSeam,cofiniteCutEpsilon]
  | succ n=>
    simp only [cofiniteCutValue,cofiniteCutOffset,cofiniteCutSlope,cofiniteCutSeam,
      Nat.cast_add,Nat.cast_one]
    have h1:(n:ℝ)+1≠0:=by positivity
    have h2:(n:ℝ)+2≠0:=by positivity
    have h3:2*(n:ℝ)+3≠0:=by positivity
    field_simp
    ring

theorem cofiniteCutValue_meet (n:ℕ) :
    cofiniteCutValue n (cofiniteCutSeam (n+1))=
      cofiniteCutValue (n+1) (cofiniteCutSeam (n+1)) := by
  rw [cofiniteCutValue_right,cofiniteCutValue_left]

theorem cofiniteCutValue_adjacent_difference (n:ℕ) (u:ℝ) :
    cofiniteCutValue n u-cofiniteCutValue (n+1) u=
      (cofiniteCutSlope n-cofiniteCutSlope (n+1))*(u-cofiniteCutSeam (n+1)) := by
  have h:=cofiniteCutValue_meet n
  dsimp [cofiniteCutValue] at h ⊢
  nlinarith

theorem cofiniteCutValue_adjacent_left (n:ℕ) (u:ℝ) (hu:u≤cofiniteCutSeam (n+1)) :
    cofiniteCutValue n u≤cofiniteCutValue (n+1) u := by
  rw [←sub_nonpos,cofiniteCutValue_adjacent_difference]
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (cofiniteCutSlope_succ_lt n).le)
    (sub_nonpos.mpr hu)

theorem cofiniteCutValue_adjacent_right (n:ℕ) (u:ℝ) (hu:cofiniteCutSeam (n+1)≤u) :
    cofiniteCutValue (n+1) u≤cofiniteCutValue n u := by
  rw [←sub_nonneg,cofiniteCutValue_adjacent_difference]
  exact mul_nonneg (sub_nonneg.mpr (cofiniteCutSlope_succ_lt n).le) (sub_nonneg.mpr hu)

theorem cofiniteCutValue_le_later (n m:ℕ) (hnm:n≤m) (u:ℝ)
    (hu:u≤cofiniteCutSeam (n+1)) : cofiniteCutValue n u≤cofiniteCutValue m u := by
  induction m,hnm using Nat.le_induction with
  | base=>exact le_rfl
  | succ m hnm ih=>
    exact ih.trans (cofiniteCutValue_adjacent_left m u
      (hu.trans (cofiniteCutSeam_mono (Nat.succ_le_succ hnm))))

theorem cofiniteCutValue_le_earlier (m n:ℕ) (hmn:m≤n) :
    ∀u:ℝ,cofiniteCutSeam n≤u→cofiniteCutValue n u≤cofiniteCutValue m u := by
  induction n,hmn using Nat.le_induction with
  | base=>intro u _hu;exact le_rfl
  | succ n hmn ih=>
    intro u hu
    exact (cofiniteCutValue_adjacent_right n u hu).trans
      (ih u ((cofiniteCutSeam_mono (Nat.le_succ n)).trans hu))

/-- The n-th genuine geodesic cut is the active cut throughout its annulus. -/
theorem cofiniteCutValue_active (n:ℕ) (u:ℝ)
    (hl:cofiniteCutSeam n≤u) (hr:u≤cofiniteCutSeam (n+1)) :
    ∀m:ℕ,cofiniteCutValue n u≤cofiniteCutValue m u := by
  intro m
  rcases le_total n m with hnm|hmn
  · exact cofiniteCutValue_le_later n m hnm u hr
  · exact cofiniteCutValue_le_earlier m n hmn u hl

theorem cofiniteCutOffset_lower (n:ℕ) : -2*cofiniteCutEpsilon≤cofiniteCutOffset n := by
  cases n with
  | zero=>exact le_rfl
  | succ n=>
    have hn:0≤(n:ℝ):=Nat.cast_nonneg n
    have h1:cofiniteCutEpsilon/((n:ℝ)+1)≤cofiniteCutEpsilon:=by
      apply (div_le_iff₀ (by positivity)).mpr
      norm_num [cofiniteCutEpsilon]
    have hden:16*((n:ℝ)+1)^2≤16*((n:ℝ)+1)*(n+2)*(2*n+3):=by
      calc
        16*((n:ℝ)+1)^2=16*((n:ℝ)+1)*(n+1):=by ring
        _≤16*((n:ℝ)+1)*(n+2):=by gcongr; linarith
        _≤16*((n:ℝ)+1)*(n+2)*(2*n+3):=by
          apply le_mul_of_one_le_right (by positivity)
          linarith
    have h2:cofiniteCutSeam (n+1)*cofiniteCutSlope (n+1)≤cofiniteCutEpsilon:=by
      simp only [cofiniteCutSeam,cofiniteCutSlope,Nat.cast_add,Nat.cast_one]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      norm_num [cofiniteCutEpsilon] at *
      nlinarith
    dsimp only [cofiniteCutOffset]
    rw [neg_div]
    linarith

theorem cofiniteCutValue_lower (n:ℕ) (u:ℝ) (hu:0≤u) :
    -2*cofiniteCutEpsilon≤cofiniteCutValue n u := by
  exact (cofiniteCutOffset_lower n).trans
    (le_add_of_nonneg_right (mul_nonneg (cofiniteCutSlope_pos n).le hu))

theorem cofiniteCutValue_strictMono (n:ℕ) : StrictMono (cofiniteCutValue n) := by
  intro u v huv
  have h:=mul_lt_mul_of_pos_left huv (cofiniteCutSlope_pos n)
  dsimp only [cofiniteCutValue]
  linarith

theorem cofiniteCutValue_neg_on_annulus (n:ℕ) (u:ℝ) (hu:u≤cofiniteCutSeam (n+1)) :
    cofiniteCutValue n u<0 := by
  have hle:cofiniteCutValue n u≤cofiniteCutValue n (cofiniteCutSeam (n+1)):=
    (cofiniteCutValue_strictMono n).monotone hu
  rw [cofiniteCutValue_right] at hle
  exact hle.trans_lt (div_neg_of_neg_of_pos (by norm_num [cofiniteCutEpsilon]) (by positivity))

def cofiniteCutNormal (a b:ℝ) : ℂ:=⟨(a-b)/2,-1/2⟩
def cofiniteCutThreshold (a b:ℝ) : ℝ:=(a+b)/2

/-- The new cuts are real affine Klein cuts of the genuine hyperbolic plane. -/
theorem cofiniteCut_klein (a b:ℝ) (z:ℍ) :
    (cofiniteCutThreshold a b-inner ℝ (cofiniteCutNormal a b)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
      (Complex.normSq (z:ℂ)+1)=a+b*Complex.normSq (z:ℂ)-z.re := by
  have hd:z.re^2+z.im^2+1≠0:=ne_of_gt (by positivity)
  norm_num [cofiniteCutThreshold,cofiniteCutNormal,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,Complex.normSq_apply]
  field_simp [hd]
  ring

theorem cofiniteCut_klein_lt (a b:ℝ) (z:ℍ) :
    z.re<a+b*Complex.normSq (z:ℂ) ↔
      inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<cofiniteCutThreshold a b := by
  have hd:0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←sub_pos,←cofiniteCut_klein,mul_pos_iff_of_pos_right hd,sub_pos]

def cofiniteCutRegion : Set ℍ:=
  {z|∀n:ℕ,z.re<cofiniteCutValue n (Complex.normSq (z:ℂ))}

theorem cofiniteCutRegion_klein : cofiniteCutRegion=
    torusKleinCutRegion (fun n=>cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n))
      (fun n=>cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n)) := by
  ext z
  simp only [cofiniteCutRegion,mem_ofPred_eq,torusKleinCutRegion,cofiniteCutValue]
  exact forall_congr' (fun n=>cofiniteCut_klein_lt _ _ z)

theorem cofiniteCutRegion_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex cofiniteCutRegion := by
  rw [cofiniteCutRegion_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem cofiniteCutRegion_mem_annulus (n:ℕ) (z:ℍ)
    (hl:cofiniteCutSeam n≤Complex.normSq (z:ℂ))
    (hr:Complex.normSq (z:ℂ)≤cofiniteCutSeam (n+1)) :
    z∈cofiniteCutRegion ↔ z.re<cofiniteCutValue n (Complex.normSq (z:ℂ)) := by
  constructor
  · exact fun hz=>hz n
  · intro hz m
    exact hz.trans_le (cofiniteCutValue_active n _ hl hr m)

theorem cofiniteCutRegion_contains_left (z:ℍ) (hz:z.re< -2*cofiniteCutEpsilon) :
    z∈cofiniteCutRegion := by
  intro n
  exact hz.trans_le (cofiniteCutValue_lower n _ (Complex.normSq_nonneg _))

/-- Every one of the distinct retained half-planes excludes the same actual compact singleton. -/
theorem cofiniteCut_excludes_i (n:ℕ) :
    ¬(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)).re<
      cofiniteCutValue n (Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num):ℂ)) := by
  have hn:1≤cofiniteCutSeam (n+1):=by
    dsimp [cofiniteCutSeam]
    have h:0≤(n:ℝ):=Nat.cast_nonneg n
    push_cast
    nlinarith [sq_nonneg (n:ℝ)]
  have h:=cofiniteCutValue_neg_on_annulus n 1 hn
  simpa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] using not_lt_of_gt h

theorem cofiniteCutSeam_unbounded (u:ℝ) : ∃N:ℕ,u<cofiniteCutSeam (N+1) := by
  obtain ⟨N,hN⟩:=exists_nat_gt (u+1)
  refine ⟨N,?_⟩
  dsimp [cofiniteCutSeam]
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) N,sq_nonneg (N:ℝ)]

theorem cofiniteCutRegion_negative (z:ℍ) (hz:z∈cofiniteCutRegion) : z.re<0 := by
  obtain ⟨N,hN⟩:=cofiniteCutSeam_unbounded (Complex.normSq (z:ℂ))
  exact (hz N).trans (cofiniteCutValue_neg_on_annulus N _ hN.le)

theorem cofiniteCutRegion_isOpen : IsOpen cofiniteCutRegion := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  obtain ⟨N,hN⟩:=cofiniteCutSeam_unbounded (Complex.normSq (z:ℂ))
  let V:Set ℍ:={w|Complex.normSq (w:ℂ)<cofiniteCutSeam (N+1)}∩
    ⋂n:Fin (N+1),{w|w.re<cofiniteCutValue n (Complex.normSq (w:ℂ))}
  have hU:Continuous (fun w:ℍ=>Complex.normSq (w:ℂ)):=
    Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe
  have hV:IsOpen V:=by
    apply IsOpen.inter
    · exact isOpen_lt hU continuous_const
    · apply isOpen_iInter_of_finite
      intro n
      exact isOpen_lt UpperHalfPlane.continuous_re
        (continuous_const.add (continuous_const.mul hU))
  refine ⟨V,?_,hV,⟨hN,mem_iInter.mpr (fun n=>hz n)⟩⟩
  rintro w ⟨hw,hcuts⟩ m
  by_cases hm:m<N+1
  · exact mem_iInter.mp hcuts ⟨m,hm⟩
  · have hNm:N≤m:=by omega
    exact (mem_iInter.mp hcuts ⟨N,Nat.lt_succ_self N⟩).trans_le
      (cofiniteCutValue_le_later N m hNm _ hw.le)

theorem cofiniteCut_klein_le (a b:ℝ) (z:ℍ) :
    z.re≤a+b*Complex.normSq (z:ℂ) ↔
      inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤cofiniteCutThreshold a b := by
  have hd:0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←sub_nonneg,←cofiniteCut_klein,mul_nonneg_iff_of_pos_right hd,sub_nonneg]

theorem cofiniteCutRegion_closure : closure cofiniteCutRegion=
    {z:ℍ|∀n:ℕ,z.re≤cofiniteCutValue n (Complex.normSq (z:ℂ))} := by
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-1/2) 1 (by norm_num)
  have hw:w∈cofiniteCutRegion:=cofiniteCutRegion_contains_left w (by
    change (-1/2:ℝ)< -2*cofiniteCutEpsilon
    norm_num [cofiniteCutEpsilon])
  rw [cofiniteCutRegion_klein,torusKleinCutRegion_closure _ _ w
    (cofiniteCutRegion_klein ▸ hw)]
  ext z
  change (∀n:ℕ,inner ℝ (cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
        z)≤cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n))↔_
  exact forall_congr' (fun n=>(cofiniteCut_klein_le _ _ z).symm)

/-- Every active equality point is on the true frontier of the convex region. -/
theorem cofiniteCutRegion_frontier_active (n:ℕ) (z:ℍ)
    (hl:cofiniteCutSeam n≤Complex.normSq (z:ℂ))
    (hr:Complex.normSq (z:ℂ)≤cofiniteCutSeam (n+1))
    (he:z.re=cofiniteCutValue n (Complex.normSq (z:ℂ))) : z∈frontier cofiniteCutRegion := by
  have hz:z∈closure cofiniteCutRegion:=by
    rw [cofiniteCutRegion_closure]
    intro m
    exact he.le.trans (cofiniteCutValue_active n _ hl hr m)
  refine ⟨hz,?_⟩
  rw [cofiniteCutRegion_isOpen.interior_eq]
  exact fun h=>(h n).ne he

def cofiniteCutPoint (n:ℕ) (u:ℝ) (hp:0<u-(cofiniteCutValue n u)^2) : ℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (cofiniteCutValue n u) (Real.sqrt (u-(cofiniteCutValue n
    u)^2))
    (Real.sqrt_pos.mpr hp)

theorem cofiniteCutPoint_normSq (n:ℕ) (u:ℝ) (hp:0<u-(cofiniteCutValue n u)^2) :
    Complex.normSq (cofiniteCutPoint n u hp:ℂ)=u := by
  simp only [cofiniteCutPoint,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  simp only [←pow_two]
  rw [Real.sq_sqrt hp.le]
  ring

theorem cofiniteCutPoint_frontier (n:ℕ) (u:ℝ) (hp:0<u-(cofiniteCutValue n u)^2)
    (hl:cofiniteCutSeam n≤u) (hr:u≤cofiniteCutSeam (n+1)) :
    cofiniteCutPoint n u hp∈frontier cofiniteCutRegion := by
  apply cofiniteCutRegion_frontier_active n
  · rwa [cofiniteCutPoint_normSq]
  · rwa [cofiniteCutPoint_normSq]
  · rw [cofiniteCutPoint_normSq]
    rfl

theorem cofiniteCutPoint_positive (n:ℕ) (hn:1≤n) (k:ℝ) (hk:1≤k∧k≤2) :
    0<cofiniteCutSeam n+k-(cofiniteCutValue n (cofiniteCutSeam n+k))^2 := by
  have hnR:1≤(n:ℝ):=by exact_mod_cast hn
  have hu:0≤cofiniteCutSeam n+k:=by
    dsimp [cofiniteCutSeam]
    nlinarith [sq_nonneg (n:ℝ)]
  have hr:cofiniteCutSeam n+k≤cofiniteCutSeam (n+1):=by
    dsimp [cofiniteCutSeam]
    push_cast
    nlinarith [sq_nonneg (n:ℝ)]
  have hlow:=cofiniteCutValue_lower n _ hu
  have hneg:=cofiniteCutValue_neg_on_annulus n _ hr
  have hsq:(-cofiniteCutValue n (cofiniteCutSeam n+k))^2≤(2*cofiniteCutEpsilon)^2:=
    (sq_le_sq₀ (by linarith) (by norm_num [cofiniteCutEpsilon])).mpr (by linarith)
  norm_num [cofiniteCutEpsilon] at hsq
  have hseam:16≤cofiniteCutSeam n:=by
    dsimp [cofiniteCutSeam]
    nlinarith [sq_nonneg (n:ℝ)]
  nlinarith

/-- Every positive index contributes two distinct true flat-frontier points. -/
theorem cofiniteCutRegion_flat_pair (n:ℕ) (hn:1≤n) :
    ∃z w:ℍ,z∈frontier cofiniteCutRegion∧w∈frontier cofiniteCutRegion∧z≠w∧
      z.re=cofiniteCutValue n (Complex.normSq (z:ℂ))∧
      w.re=cofiniteCutValue n (Complex.normSq (w:ℂ))∧
      -1<z.re∧z.re<0∧-1<w.re∧w.re<0 := by
  have hp:=cofiniteCutPoint_positive n hn 1 (by norm_num)
  have hq:=cofiniteCutPoint_positive n hn 2 (by norm_num)
  let z:=cofiniteCutPoint n (cofiniteCutSeam n+1) hp
  let w:=cofiniteCutPoint n (cofiniteCutSeam n+2) hq
  have hzU:Complex.normSq (z:ℂ)=cofiniteCutSeam n+1:=cofiniteCutPoint_normSq _ _ _
  have hwU:Complex.normSq (w:ℂ)=cofiniteCutSeam n+2:=cofiniteCutPoint_normSq _ _ _
  have hnR:1≤(n:ℝ):=by exact_mod_cast hn
  have h1:cofiniteCutSeam n+1≤cofiniteCutSeam (n+1):=by
    dsimp [cofiniteCutSeam];push_cast;nlinarith
  have h2:cofiniteCutSeam n+2≤cofiniteCutSeam (n+1):=by
    dsimp [cofiniteCutSeam];push_cast;nlinarith
  have hzF:z∈frontier cofiniteCutRegion:=cofiniteCutPoint_frontier n _ hp (by linarith) h1
  have hwF:w∈frontier cofiniteCutRegion:=cofiniteCutPoint_frontier n _ hq (by linarith) h2
  have hzlo:=cofiniteCutValue_lower n (cofiniteCutSeam n+1) (by
    dsimp [cofiniteCutSeam];positivity)
  have hwlo:=cofiniteCutValue_lower n (cofiniteCutSeam n+2) (by
    dsimp [cofiniteCutSeam];positivity)
  refine ⟨z,w,hzF,hwF,?_,?_,?_,?_,?_,?_,?_⟩
  · intro he
    have heU:=congrArg (fun z:ℍ=>Complex.normSq (z:ℂ)) he
    rw [hzU,hwU] at heU
    linarith
  · rw [hzU];rfl
  · rw [hwU];rfl
  · change -1<cofiniteCutValue n (cofiniteCutSeam n+1)
    norm_num [cofiniteCutEpsilon] at hzlo
    linarith
  · change cofiniteCutValue n (cofiniteCutSeam n+1)<0
    exact cofiniteCutValue_neg_on_annulus n _ h1
  · change -1<cofiniteCutValue n (cofiniteCutSeam n+2)
    norm_num [cofiniteCutEpsilon] at hwlo
    linarith
  · change cofiniteCutValue n (cofiniteCutSeam n+2)<0
    exact cofiniteCutValue_neg_on_annulus n _ h2


/-- The annular seams are unchanged from the actual infinite-side group construction. -/
theorem cofiniteCutSeam_center (n:ℕ) :
    cofiniteCutSeam n=(infiniteSideCenter n-2)^2 ∧
    cofiniteCutSeam (n+1)=(infiniteSideCenter n+2)^2 := by
  dsimp [cofiniteCutSeam,infiniteSideCenter]
  push_cast
  constructor <;> ring

theorem cofiniteCut_klein_gt (a b:ℝ) (z:ℍ) :
    a+b*Complex.normSq (z:ℂ)<z.re ↔
      inner ℝ (-cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<
        -cofiniteCutThreshold a b := by
  have h:=cofiniteCut_klein a b z
  have hp:0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [inner_neg_left]
  constructor <;> intro hh
  · have hs:cofiniteCutThreshold a b-
        inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<0:=by
      by_contra! hnonneg
      have hprod:=mul_nonneg hnonneg hp.le
      linarith
    linarith
  · have hs:(cofiniteCutThreshold a b-
        inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
        (Complex.normSq (z:ℂ)+1)<0:=mul_neg_of_neg_of_pos (by linarith) hp
    linarith

def cofiniteRightWindow (n:ℕ) : Set ℍ:=
  {z|cofiniteCutValue n (Complex.normSq (z:ℂ))<z.re ∧
    (infiniteSideCenter n-2)^2<Complex.normSq (z:ℂ) ∧
    Complex.normSq (z:ℂ)<(infiniteSideCenter n+2)^2}

def cofiniteWindowNormals (n:ℕ) : Fin 3→ℂ:=
  ![-cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n),
    torusCircleNormal (-(infiniteSideCenter n-2)) (infiniteSideCenter n-2),
    -torusCircleNormal (-(infiniteSideCenter n+2)) (infiniteSideCenter n+2)]

def cofiniteWindowThresholds (n:ℕ) : Fin 3→ℝ:=
  ![-cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n),
    torusCircleThreshold (-(infiniteSideCenter n-2)) (infiniteSideCenter n-2),
    -torusCircleThreshold (-(infiniteSideCenter n+2)) (infiniteSideCenter n+2)]

theorem cofiniteRightWindow_klein (n:ℕ) : cofiniteRightWindow n=
    torusKleinCutRegion (cofiniteWindowNormals n) (cofiniteWindowThresholds n) := by
  ext z
  constructor
  · rintro ⟨hx,hi,ho⟩ i
    fin_cases i
    · exact (cofiniteCut_klein_gt _ _ z).mp hx
    · exact (torusCircleQ_klein_pos_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin];linarith)
    · exact (torusCircleQ_klein_neg_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin];linarith)
  · intro h
    have hx:cofiniteCutValue n (Complex.normSq (z:ℂ))<z.re:=
      (cofiniteCut_klein_gt _ _ z).mpr (h (0:Fin 3))
    have hi:0<torusCircleQ (-(infiniteSideCenter n-2)) (infiniteSideCenter n-2) z:=
      (torusCircleQ_klein_pos_iff _ _ z).mpr (h (1:Fin 3))
    have ho:torusCircleQ (-(infiniteSideCenter n+2)) (infiniteSideCenter n+2) z<0:=
      (torusCircleQ_klein_neg_iff _ _ z).mpr (h (2:Fin 3))
    rw [infiniteSide_circleQ_origin] at hi ho
    exact ⟨hx,by linarith,by linarith⟩

theorem cofiniteRightWindow_isOpen (n:ℕ) : IsOpen (cofiniteRightWindow n) := by
  rw [cofiniteRightWindow_klein]
  exact torusKleinCutRegion_isOpen _ _

theorem cofiniteRightWindow_hConvex (n:ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (cofiniteRightWindow n) := by
  rw [cofiniteRightWindow_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem infiniteSideRightWindow_subset_cofinite (n:ℕ) :
    infiniteSideRightWindow (infiniteSideCenter n)⊆cofiniteRightWindow n := by
  intro z hz
  refine ⟨lt_trans (cofiniteCutValue_neg_on_annulus n _ ?_) hz.1,hz.2⟩
  rw [(cofiniteCutSeam_center n).2]
  exact hz.2.2.le

theorem cofiniteRightWindow_of_circle (n:ℕ) (z:ℍ)
    (hz:infiniteSideCircleQ (infiniteSideCenter n) z≤1) : z∈cofiniteRightWindow n :=
  infiniteSideRightWindow_subset_cofinite n
    (infiniteSideRightWindow_of_circle _ (infiniteSideCenter_two_le n) z hz)

theorem cofinite_inverse_window_of_exterior (n:ℕ) (z:ℍ)
    (hz:1≤ infiniteSideCircleQ (-infiniteSideCenter n) z) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
      n)))⁻¹ z∈cofiniteRightWindow n :=
  infiniteSideRightWindow_subset_cofinite n
    (infiniteSide_inverse_window_of_exterior _ (infiniteSideCenter_two_le n) z hz)

theorem cofiniteRightWindow_re_lower (n:ℕ) (z:ℍ) (hz:z∈cofiniteRightWindow n) :
    -2*cofiniteCutEpsilon<z.re :=
  lt_of_le_of_lt (cofiniteCutValue_lower n _ (Complex.normSq_nonneg _)) hz.1

theorem cofiniteRightWindow_disjoint (n m:ℕ) (hne:n≠m) :
    Disjoint (cofiniteRightWindow n) (cofiniteRightWindow m) := by
  apply disjoint_left.mpr
  intro z hn hm
  rcases lt_or_gt_of_ne hne with h|h
  · have hnm:(n:ℝ)+1≤m:=by exact_mod_cast h
    have hsq:cofiniteCutSeam (n+1)≤cofiniteCutSeam m:=
      cofiniteCutSeam_mono (by omega)
    rw [(cofiniteCutSeam_center n).2,(cofiniteCutSeam_center m).1] at hsq
    exact (not_lt_of_ge (hsq.trans hm.2.1.le)) hn.2.2
  · have hmn:(m:ℝ)+1≤n:=by exact_mod_cast h
    have hsq:cofiniteCutSeam (m+1)≤cofiniteCutSeam n:=
      cofiniteCutSeam_mono (by omega)
    rw [(cofiniteCutSeam_center m).2,(cofiniteCutSeam_center n).1] at hsq
    exact (not_lt_of_ge (hsq.trans hn.2.1.le)) hm.2.2

theorem cofiniteRightWindow_other_circle (n m:ℕ) (hne:n≠m) (z:ℍ)
    (hz:z∈cofiniteRightWindow n) : 1< infiniteSideCircleQ (infiniteSideCenter m) z := by
  by_contra hm
  exact disjoint_left.mp (cofiniteRightWindow_disjoint n m hne) hz
    (cofiniteRightWindow_of_circle m z (le_of_not_gt hm))

/-- A reassembly of the already verified actual group, with curved envelope cuts. -/
def cofinitePolygon : Set ℍ:=
  {z|z∈cofiniteCutRegion ∧∀n:ℕ,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
      n)))⁻¹ z∈cofiniteRightWindow n}

theorem cofinitePolygon_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex cofinitePolygon := by
  intro z hz w hw u hu
  refine ⟨cofiniteCutRegion_hConvex z hz.1 w hw.1 hu,?_⟩
  intro n
  exact ((cofiniteRightWindow_hConvex n).isometry_preimage
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
      n)))⁻¹).isometry)
    z (hz.2 n) w (hw.2 n) hu

theorem cofinitePolygon_isOpen : IsOpen cofinitePolygon := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  obtain ⟨N,hN⟩:=exists_nat_gt (-z.re+3)
  let V:Set ℍ:=cofiniteCutRegion∩{w|z.re-1<w.re}∩
    ⋂n:Fin N,(fun w:ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
      (infiniteSideCenter n)))⁻¹ w)⁻¹'
      cofiniteRightWindow n
  have hV:IsOpen V:=by
    refine (cofiniteCutRegion_isOpen.inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_re)).inter ?_
    exact isOpen_iInter_of_finite (fun n=>(cofiniteRightWindow_isOpen n).preimage
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        n)))⁻¹).continuous)
  refine ⟨V,?_,hV,?_⟩
  · rintro w ⟨⟨hw,hclose⟩,hwindow⟩
    change z.re-1<w.re at hclose
    refine ⟨hw,fun n=>?_⟩
    by_cases hn:n<N
    · exact mem_iInter.mp hwindow ⟨n,hn⟩
    · have hnr:(N:ℝ)≤n:=by exact_mod_cast Nat.le_of_not_gt hn
      apply cofinite_inverse_window_of_exterior n w
      exact (infiniteSideCircleQ_large_of_re (-infiniteSideCenter n) w
        (Or.inr (by dsimp only [infiniteSideCenter];linarith [Nat.cast_nonneg (α:=ℝ) n]))).le
  · exact ⟨⟨hz.1,by change z.re-1<z.re;linarith⟩,mem_iInter.mpr (fun n=>hz.2 n)⟩

theorem cofinitePolygon_contains_exterior (z:ℍ) (hz:z∈cofiniteCutRegion)
    (hc:∀n:ℕ,1≤ infiniteSideCircleQ (-infiniteSideCenter n) z) : z∈cofinitePolygon :=
  ⟨hz,fun n=>cofinite_inverse_window_of_exterior n z (hc n)⟩

theorem cofinitePolygon_nonempty : cofinitePolygon.Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-1/2) 1 (by norm_num),cofinitePolygon_contains_exterior _ ?_ ?_⟩
  · apply cofiniteCutRegion_contains_left
    change (-1/2:ℝ)< -2*cofiniteCutEpsilon
    norm_num [cofiniteCutEpsilon]
  · intro n
    exact (infiniteSideCircleQ_large_of_re (-infiniteSideCenter n) _ (Or.inr (by
      change -infiniteSideCenter n+1≤(-1/2:ℝ)
      linarith [infiniteSideCenter_two_le n]))).le

def cofinitePieces : Option ℕ→Set ℍ
  | none=>infiniteSideBase∩cofiniteCutRegion
  | some n=>infiniteSideBase∩cofiniteRightWindow n

def cofiniteAssembly : Set ℍ:=⋃j:Option ℕ,infiniteSideLabels j '' cofinitePieces j

theorem cofinitePieces_subset (j:Option ℕ) : cofinitePieces j⊆infiniteSideBase := by
  cases j <;> exact inter_subset_left

theorem cofinitePieces_unique (j k:Option ℕ) (z:ℍ)
    (hj:z∈cofinitePieces j) (hk:z∈cofinitePieces k) : j=k := by
  cases j with
  | none=>
    cases k with
    | none=>rfl
    | some n=>
      exact False.elim (not_lt_of_ge (hj.2 n).le hk.2.1)
  | some n=>
    cases k with
    | none=>exact False.elim (not_lt_of_ge (hk.2 n).le hj.2.1)
    | some m=>
      congr 1
      by_contra hne
      exact disjoint_left.mp (cofiniteRightWindow_disjoint n m hne) hj.2 hk.2

theorem cofiniteAssembly_isOpen : IsOpen cofiniteAssembly := by
  apply isOpen_iUnion
  intro j
  apply (infiniteSideLabels j).toHomeomorph.isOpenMap
  cases j with
  | none=>exact infiniteSideBase_isOpen.inter cofiniteCutRegion_isOpen
  | some n=>exact infiniteSideBase_isOpen.inter (cofiniteRightWindow_isOpen n)

theorem cofiniteAssembly_wandering (g:ℍ≃ᵢℍ) (hg:g∈infiniteSideNativeGroup) (hne:g≠1) :
    Disjoint (g•cofiniteAssembly) cofiniteAssembly :=
  indexed_reassembly_wandering infiniteSideNativeGroup infiniteSideBase
    cofinitePieces infiniteSideLabels cofinitePieces_subset cofinitePieces_unique
    infiniteSideLabels_mem infiniteSideBase_wandering g hg hne

theorem cofiniteAssembly_subset : cofiniteAssembly⊆cofinitePolygon := by
  intro z hz
  obtain ⟨j,w,hw,rfl⟩:=mem_iUnion.mp hz
  cases j with
  | none=>
    change w∈cofinitePolygon
    exact cofinitePolygon_contains_exterior w hw.2
      (fun n=>((infiniteSideBase_mem_iff w).mp hw.1 n).2.le)
  | some n=>
    let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w
    change z∈cofinitePolygon
    have hzq:infiniteSideCircleQ (-infiniteSideCenter n) z<1:=
      infiniteSide_label_image_circle n w hw.1
    have hx:=infiniteSideCircleQ_small_re (-infiniteSideCenter n) z hzq.le
    refine ⟨cofiniteCutRegion_contains_left z ?_,fun m=>?_⟩
    · norm_num [cofiniteCutEpsilon]
      linarith [infiniteSideCenter_two_le n]
    · by_cases hmn:m=n
      · subst m
        simpa only [z,IsometryEquiv.inv_apply_self] using hw.2
      · have hu:z∈infiniteSideSector (infiniteSideCenter n)∪
            infiniteSideSector (infiniteSideCenter m):=by
          rw [infiniteSideSector_cover n m (Ne.symm hmn)];trivial
        have hm:1< infiniteSideCircleQ (-infiniteSideCenter m) z:=by
          rcases hu with hn|hm
          · exact False.elim ((not_lt_of_ge hzq.le) hn.2)
          · exact hm.2
        exact cofinite_inverse_window_of_exterior m z hm.le


open MeasureTheory

theorem cofinitePolygon_outside_seams :
    cofinitePolygon∩infiniteSideSeamsᶜ⊆cofiniteAssembly := by
  intro z ⟨hz,hseam⟩
  have hx:=cofiniteCutRegion_negative z hz.1
  by_cases hall:∀n:ℕ,1< infiniteSideCircleQ (-infiniteSideCenter n) z
  · have hb:z∈infiniteSideBase:=by
      rw [infiniteSideBase_mem_iff]
      intro n
      exact ⟨infiniteSideCircleQ_large_of_re _ z
        (Or.inl (by linarith [infiniteSideCenter_two_le n])),hall n⟩
    exact mem_iUnion.mpr ⟨none,z,⟨hb,hz.1⟩,rfl⟩
  · push Not at hall
    obtain ⟨n,hn⟩:=hall
    have hne:infiniteSideCircleQ (-infiniteSideCenter n) z≠1:=by
      intro he
      exact hseam (mem_iUnion.mpr ⟨n,he⟩)
    have hlt:infiniteSideCircleQ (-infiniteSideCenter n) z<1:=lt_of_le_of_ne hn hne
    let w:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ z
    have he:infiniteSideSL (infiniteSideCenter n)•w=z:=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        n))).apply_inv_self z
    have hwin:w∈cofiniteRightWindow n:=hz.2 n
    have hi:=infiniteSideSL_circle_identity (infiniteSideCenter n) w
    rw [he] at hi
    have hqw:1< infiniteSideCircleQ (infiniteSideCenter n) w:=by
      have hp:=infiniteSideCircleQ_pos (infiniteSideCenter n) w
      have hnonneg:0≤ infiniteSideCircleQ (-infiniteSideCenter n) z:=
        Complex.normSq_nonneg _
      by_contra hh
      have hle:=le_of_not_gt hh
      nlinarith
    have hb:w∈infiniteSideBase:=by
      rw [infiniteSideBase_mem_iff]
      intro m
      constructor
      · by_cases hmn:m=n
        · simpa only [hmn] using hqw
        · exact cofiniteRightWindow_other_circle n m (Ne.symm hmn) w hwin
      · apply infiniteSideCircleQ_large_of_re _ w
        apply Or.inr
        have hlow:=cofiniteRightWindow_re_lower n w hwin
        norm_num [cofiniteCutEpsilon] at hlow
        linarith [infiniteSideCenter_two_le m]
    exact mem_iUnion.mpr ⟨some n,w,⟨hb,hwin⟩,he⟩

theorem cofinitePolygon_subset_closure_assembly : cofinitePolygon⊆closure cofiniteAssembly := by
  let :Measure.IsOpenPosMeasure (volume:Measure ℍ):=
    ⟨fun U hU hn=>ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.native_open_volume_pos hU hn)⟩
  have hd:Dense infiniteSideSeamsᶜ:=
    (volume:Measure ℍ).dense_of_ae (measure_eq_zero_iff_ae_notMem.mp infiniteSideSeams_null)
  exact (hd.open_subset_closure_inter cofinitePolygon_isOpen).trans
    (closure_mono cofinitePolygon_outside_seams)

theorem cofinitePolygon_wandering (g:ℍ≃ᵢℍ) (hg:g∈infiniteSideNativeGroup) (hne:g≠1) :
    Disjoint (g•cofinitePolygon) cofinitePolygon :=
  open_closure_wandering infiniteSideNativeGroup cofiniteAssembly cofinitePolygon
    cofiniteAssembly_isOpen cofinitePolygon_isOpen
    cofinitePolygon_subset_closure_assembly cofiniteAssembly_wandering g hg hne

theorem cofinitePolygon_frontier_null : volume (frontier cofinitePolygon)=0:=
  parabolicFord_hConvex_frontier_volume_zero cofinitePolygon_hConvex

theorem cofinitePieces_locallyFinite : LocallyFinite cofinitePieces := by
  intro z
  obtain ⟨N,hN⟩:=exists_nat_gt ‖(z:ℂ)‖
  let U:Set ℍ:={w|‖(w:ℂ)‖<N}
  have hU:U∈𝓝 z:=
    (isOpen_lt UpperHalfPlane.continuous_coe.norm continuous_const).mem_nhds hN
  refine ⟨U,hU,?_⟩
  have hf:({none}∪Option.some '' Iio N:Set (Option ℕ)).Finite:=
    (finite_singleton none).union ((finite_Iio N).image Option.some)
  apply hf.subset
  intro j hj
  cases j with
  | none=>exact Or.inl (mem_singleton _)
  | some n=>
    apply Or.inr
    refine ⟨n,?_,rfl⟩
    obtain ⟨w,hw,hwn⟩:=hj
    have hlow:(4*(n:ℝ))^2<‖(w:ℂ)‖^2:=by
      have h:=hw.2.2.1
      change (infiniteSideCenter n-2)^2<Complex.normSq (w:ℂ) at h
      simpa only [infiniteSideCenter,add_sub_cancel_right,Complex.normSq_eq_norm_sq] using h
    have hbound:4*(n:ℝ)<‖(w:ℂ)‖:=by
      nlinarith [norm_nonneg (w:ℂ),Nat.cast_nonneg (α:=ℝ) n]
    have hwn':‖(w:ℂ)‖<N:=hwn
    have hnN:(n:ℝ)<N:=by linarith [Nat.cast_nonneg (α:=ℝ) n]
    exact_mod_cast hnN

def cofiniteSourceCuts : Set ℍ:=frontier cofiniteCutRegion∪infiniteSideSourceCuts

theorem cofiniteSourceCuts_null : volume cofiniteSourceCuts=0:=
  measure_union_null (parabolicFord_hConvex_frontier_volume_zero cofiniteCutRegion_hConvex)
    infiniteSideSourceCuts_null

theorem cofinite_exists_radial_window (z:ℍ)
    (hcut:∀n:ℕ,Complex.normSq (z:ℂ)≠(4*(n:ℝ))^2) :
    ∃n:ℕ,(infiniteSideCenter n-2)^2<Complex.normSq (z:ℂ)∧
      Complex.normSq (z:ℂ)<(infiniteSideCenter n+2)^2 := by
  let n:=Nat.floor (‖(z:ℂ)‖/4)
  have hl:=Nat.floor_le (show 0≤‖(z:ℂ)‖/4 by positivity)
  have hu:=Nat.lt_floor_add_one (‖(z:ℂ)‖/4)
  have hlow:4*(n:ℝ)≤‖(z:ℂ)‖:=by dsimp only [n];linarith
  have hupp:‖(z:ℂ)‖<4*(n:ℝ)+4:=by dsimp only [n];linarith
  refine ⟨n,?_,?_⟩
  · have hsq:=(sq_le_sq₀ (by positivity:0≤4*(n:ℝ)) (norm_nonneg (z:ℂ))).mpr hlow
    have hne:=Ne.symm (hcut n)
    rw [Complex.normSq_eq_norm_sq] at hne
    have hh:=lt_of_le_of_ne hsq hne
    simpa only [infiniteSideCenter,add_sub_cancel_right,Complex.normSq_eq_norm_sq] using hh
  · have hh:=(sq_lt_sq₀ (norm_nonneg (z:ℂ))
      (by positivity:0≤4*(n:ℝ)+4)).mpr hupp
    change Complex.normSq (z:ℂ)<(4*(n:ℝ)+2+2)^2
    rw [Complex.normSq_eq_norm_sq]
    convert hh using 1;ring

theorem cofiniteBase_outside_cuts :
    infiniteSideBase∩cofiniteSourceCutsᶜ⊆⋃j,cofinitePieces j := by
  intro z ⟨hz,hcut⟩
  by_cases hq:z∈cofiniteCutRegion
  · exact mem_iUnion.mpr ⟨none,⟨hz,hq⟩⟩
  · obtain ⟨n,hnl,hnr⟩:=cofinite_exists_radial_window z (fun n he=>
      hcut (Or.inr (Or.inr (mem_iUnion.mpr ⟨n,he⟩))))
    have hl:cofiniteCutSeam n≤Complex.normSq (z:ℂ):=by
      rw [(cofiniteCutSeam_center n).1];exact hnl.le
    have hr:Complex.normSq (z:ℂ)≤cofiniteCutSeam (n+1):=by
      rw [(cofiniteCutSeam_center n).2];exact hnr.le
    have hge:cofiniteCutValue n (Complex.normSq (z:ℂ))≤z.re:=by
      apply le_of_not_gt
      intro hh
      exact hq ((cofiniteCutRegion_mem_annulus n z hl hr).mpr hh)
    have hne:z.re≠cofiniteCutValue n (Complex.normSq (z:ℂ)):=by
      intro he
      exact hcut (Or.inl (cofiniteCutRegion_frontier_active n z hl hr he))
    exact mem_iUnion.mpr ⟨some n,⟨hz,lt_of_le_of_ne hge hne.symm,hnl,hnr⟩⟩

theorem cofiniteBase_subset_closure_pieces : infiniteSideBase⊆closure (⋃j,cofinitePieces j) := by
  let :Measure.IsOpenPosMeasure (volume:Measure ℍ):=
    ⟨fun U hU hn=>ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.native_open_volume_pos hU hn)⟩
  have hd:Dense cofiniteSourceCutsᶜ:=
    (volume:Measure ℍ).dense_of_ae (measure_eq_zero_iff_ae_notMem.mp cofiniteSourceCuts_null)
  exact (hd.open_subset_closure_inter infiniteSideBase_isOpen).trans
    (closure_mono cofiniteBase_outside_cuts)

theorem cofinitePolygon_closure_meetsEveryOrbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit infiniteSideNativeGroup ℍ (closure cofinitePolygon) := by
  intro z
  obtain ⟨g,hg⟩ := infiniteSideBase_closure_meetsEveryOrbit z
  have hc : closure infiniteSideBase ⊆ ⋃j,closure (cofinitePieces j) := by
    rw [← cofinitePieces_locallyFinite.closure_iUnion]
    exact (closure_mono cofiniteBase_subset_closure_pieces).trans_eq closure_closure
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc hg)
  let k : infiniteSideNativeGroup :=
    ⟨infiniteSideLabels j,infiniteSideLabels_mem j⟩ * g
  refine ⟨k,?_⟩
  have him : infiniteSideLabels j (g.val z) ∈
      closure (infiniteSideLabels j '' cofinitePieces j) := by
    have he : infiniteSideLabels j '' closure (cofinitePieces j) =
        closure (infiniteSideLabels j '' cofinitePieces j) :=
      (infiniteSideLabels j).toHomeomorph.image_closure _
    rw [← he]
    exact mem_image_of_mem _ hj
  apply closure_mono cofiniteAssembly_subset
  exact closure_mono (subset_iUnion (fun j => infiniteSideLabels j '' cofinitePieces j) j) him

theorem cofinitePolygon_fundamental :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideNativeGroup ℍ volume cofinitePolygon := by
  refine ⟨cofinitePolygon_isOpen,
    ⟨cofinitePolygon_nonempty,cofinitePolygon_hConvex.isPreconnected⟩,?_,
    cofinitePolygon_frontier_null⟩
  apply exists_fundamentalSet_between _ _ subset_closure cofinitePolygon_closure_meetsEveryOrbit
  intro x hx y hy hxy
  obtain ⟨g,hg⟩ := (Quotient.exact hxy : MulAction.orbitRel infiniteSideNativeGroup ℍ x y)
  change g.val y=x at hg
  by_cases he : g.val=1
  · rw [he] at hg
    exact hg.symm
  · exact False.elim (disjoint_left.mp (cofinitePolygon_wandering g.val g.property he)
      ⟨y,hy,hg⟩ hx)

theorem cofinite_imagePieces_locallyFinite :
    LocallyFinite (fun j => infiniteSideLabels j '' cofinitePieces j) := by
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt (-z.re+3)
  let U : Set ℍ := {w | z.re-1 < w.re}
  have hzU : z ∈ U := by change z.re-1 < z.re; linarith
  have hoU : IsOpen U := isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have hU : U ∈ 𝓝 z := hoU.mem_nhds hzU
  refine ⟨U,hU,?_⟩
  have hf : ({none} ∪ Option.some '' Iio N : Set (Option ℕ)).Finite :=
    (finite_singleton none).union ((finite_Iio N).image Option.some)
  apply hf.subset
  intro j hj
  cases j with
  | none => exact Or.inl (mem_singleton _)
  | some n =>
    apply Or.inr
    refine ⟨n,?_,rfl⟩
    obtain ⟨v,⟨w,hw,rfl⟩,hv⟩ := hj
    have hq := infiniteSide_label_image_circle n w hw.1
    have hx := infiniteSideCircleQ_small_re _ _ hq.le
    have hv' : z.re-1 < (infiniteSideLabels (some n) w).re := hv
    have hnN : (n:ℝ) < N := by
      change z.re-1 < (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        n)) w).re at hv'
      have hh : infiniteSideCenter n < 2-z.re := by linarith [hx.2,hv']
      dsimp only [infiniteSideCenter] at hh
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hnN

theorem cofinitePolygon_closure_pieces :
    closure cofinitePolygon =
      ⋃ j,closure (infiniteSideLabels j '' cofinitePieces j) := by
  calc
    closure cofinitePolygon = closure cofiniteAssembly := by
      apply subset_antisymm
      · exact (closure_mono cofinitePolygon_subset_closure_assembly).trans_eq closure_closure
      · exact closure_mono cofiniteAssembly_subset
    _ = _ := cofinite_imagePieces_locallyFinite.closure_iUnion

theorem cofinitePolygon_native_compact_hits (K : Set ℍ) (hK : IsCompact K) :
    {g : infiniteSideNativeGroup |
      (g.val '' closure cofinitePolygon ∩ K).Nonempty}.Finite := by
  let A : Set infiniteSideNativeGroup :=
    {h | (h.val '' closure infiniteSideBase ∩ K).Nonempty}
  let C (h : infiniteSideNativeGroup) : Set ℍ := h.val.symm '' K
  let J (h : infiniteSideNativeGroup) : Set (Option ℕ) :=
    {j | (closure (cofinitePieces j) ∩ C h).Nonempty}
  let L (j : Option ℕ) : infiniteSideNativeGroup :=
    ⟨infiniteSideLabels j,infiniteSideLabels_mem j⟩
  have hA : A.Finite := infiniteSideBase_native_compact_hits K hK
  have hJ (h : infiniteSideNativeGroup) : (J h).Finite :=
    cofinitePieces_locallyFinite.closure.finite_nonempty_inter_compact
      (hK.image h.val.symm.continuous)
  have hf : (⋃ h ∈ A, (fun j => h * (L j)⁻¹) '' J h).Finite :=
    hA.biUnion (fun h _ => (hJ h).image _)
  apply hf.subset
  rintro g ⟨x,⟨y,hy,hgy⟩,hxK⟩
  rw [cofinitePolygon_closure_pieces] at hy
  obtain ⟨j,hj⟩ := mem_iUnion.mp hy
  have he : infiniteSideLabels j '' closure (cofinitePieces j) =
      closure (infiniteSideLabels j '' cofinitePieces j) :=
    (infiniteSideLabels j).toHomeomorph.image_closure _
  rw [← he] at hj
  obtain ⟨w,hw,hwL⟩ := hj
  let h := g * L j
  have hhw : h.val w = x := by
    change g.val (infiniteSideLabels j w)=x
    rw [hwL]
    exact hgy
  have hhA : h ∈ A :=
    ⟨x,⟨w,closure_mono (cofinitePieces_subset j) hw,hhw⟩,hxK⟩
  have hjJ : j ∈ J h := by
    refine ⟨w,hw,x,hxK,?_⟩
    rw [← hhw,h.val.symm_apply_apply]
  refine mem_iUnion.mpr ⟨h,mem_iUnion.mpr ⟨hhA,j,hjJ,?_⟩⟩
  dsimp only [h]
  group

theorem cofinitePolygon_native_locallyFinite :
    LocallyFinite (fun g : infiniteSideNativeGroup =>
      g.val '' closure cofinitePolygon) := by
  intro x
  obtain ⟨K,hK,hx⟩ := exists_compact_mem_nhds x
  exact ⟨K,hx,cofinitePolygon_native_compact_hits K hK⟩



theorem cofinitePolygon_original_fundamental :
    let :=infiniteSideData.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideGroup ℍ volume cofinitePolygon := by
  let :=infiniteSideData.nativeAction
  have he (g:infiniteSideGroup) (z:ℍ) :
      (Homeomorph.refl ℍ) (g•z)=
        infiniteSideNativeOriginalEquiv.symm g•(Homeomorph.refl ℍ) z := by
    change g•z=(infiniteSideNativeOriginalEquiv.symm g).val z
    have h:=infiniteSideNativeOriginalEquiv_action (infiniteSideNativeOriginalEquiv.symm g) z
    rwa [infiniteSideNativeOriginalEquiv.apply_symm_apply] at h
  simpa using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage infiniteSideNativeOriginalEquiv.symm
    (Homeomorph.refl ℍ) he cofinitePolygon_fundamental

theorem cofinitePolygon_original_compact_hits (K:Set ℍ) (hK:IsCompact K) :
    let :=infiniteSideData.nativeAction
    {g:infiniteSideGroup|(g•closure cofinitePolygon∩K).Nonempty}.Finite := by
  let :=infiniteSideData.nativeAction
  have hf:=(cofinitePolygon_native_compact_hits K hK).image infiniteSideNativeOriginalEquiv
  apply hf.subset
  rintro g ⟨x,⟨z,hz,hgz⟩,hx⟩
  refine ⟨infiniteSideNativeOriginalEquiv.symm g,?_,infiniteSideNativeOriginalEquiv.apply_symm_apply g⟩
  refine ⟨x,⟨z,hz,?_⟩,hx⟩
  have he:=infiniteSideNativeOriginalEquiv_action (infiniteSideNativeOriginalEquiv.symm g) z
  rw [infiniteSideNativeOriginalEquiv.apply_symm_apply] at he
  exact he.symm.trans hgz

def cofiniteOriginalPolygon : Set infiniteSideData.cayleyData.domain.carrier:=
  infiniteSideData.cayleyCoordinate '' cofinitePolygon

theorem cofiniteOriginalPolygon_convexPolygon :
    IsConvexFuchsianPolygon infiniteSideData.cayleyData cofiniteOriginalPolygon :=
  infiniteSideData.cayley_polygon cofinitePolygon_original_fundamental
    cofinitePolygon_hConvex cofinitePolygon_original_compact_hits

theorem cofinitePolygon_mem_strip (z:ℍ) (hz:-1<z.re) :
    z∈cofinitePolygon ↔ z∈cofiniteCutRegion := by
  constructor
  · exact fun h=>h.1
  · intro h
    apply cofinitePolygon_contains_exterior z h
    intro n
    apply (infiniteSideCircleQ_large_of_re (-infiniteSideCenter n) z _).le
    exact Or.inr (by linarith [infiniteSideCenter_two_le n])

theorem cofinitePolygon_frontier_strip (z:ℍ) (hz:-1<z.re)
    (hf:z∈frontier cofiniteCutRegion) : z∈frontier cofinitePolygon := by
  have hU:IsOpen {w:ℍ|-1<w.re}:=isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have hcl:z∈closure cofinitePolygon:=by
    apply closure_mono (t:=cofinitePolygon) _ (hU.inter_closure ⟨hz,frontier_subset_closure hf⟩)
    exact fun w hw=>(cofinitePolygon_mem_strip w hw.1).mpr hw.2
  rw [frontier,cofinitePolygon_isOpen.interior_eq]
  refine ⟨hcl,?_⟩
  intro hm
  have hq:=hm.1
  rw [frontier,cofiniteCutRegion_isOpen.interior_eq] at hf
  exact hf.2 hq

theorem cofiniteCut_klein_eq (a b:ℝ) (z:ℍ) :
    z.re=a+b*Complex.normSq (z:ℂ) ↔
      inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)=cofiniteCutThreshold a b := by
  have h:=cofiniteCut_klein a b z
  have hd:Complex.normSq (z:ℂ)+1≠0:=ne_of_gt (by linarith [Complex.normSq_nonneg (z:ℂ)])
  constructor
  · intro he
    have hp:(cofiniteCutThreshold a b-
        inner ℝ (cofiniteCutNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
        (Complex.normSq (z:ℂ)+1)=0:=by rw [h];linarith
    have hz:=(mul_eq_zero.mp hp).resolve_right hd
    linarith
  · intro he
    rw [he,sub_self,zero_mul] at h
    linarith

theorem cofiniteCutNormal_ne_zero (a b:ℝ) : cofiniteCutNormal a b≠0 := by
  intro he
  have hi:=congrArg Complex.im he
  norm_num [cofiniteCutNormal] at hi

theorem cofiniteCutLine_normSq_injective (n:ℕ) {z w:ℍ}
    (hz:z.re=cofiniteCutValue n (Complex.normSq (z:ℂ)))
    (hw:w.re=cofiniteCutValue n (Complex.normSq (w:ℂ)))
    (he:Complex.normSq (z:ℂ)=Complex.normSq (w:ℂ)) : z=w := by
  have hre:z.re=w.re:=by rw [hz,hw,he]
  have him:z.im=w.im:=by
    simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] at he
    rw [hre] at he
    nlinarith [z.im_pos,w.im_pos]
  apply UpperHalfPlane.ext
  exact Complex.ext hre him

theorem cofinitePolygon_flat_pair (n:ℕ) (hn:1≤n) :
    ∃z w:ℍ,z∈frontier cofinitePolygon∧w∈frontier cofinitePolygon∧z≠w∧
      z.re=cofiniteCutValue n (Complex.normSq (z:ℂ))∧
      w.re=cofiniteCutValue n (Complex.normSq (w:ℂ)) := by
  obtain ⟨z,w,hz,hw,hne,hze,hwe,hzl,_,hwl,_⟩:=cofiniteCutRegion_flat_pair n hn
  exact ⟨z,w,cofinitePolygon_frontier_strip z hzl hz,cofinitePolygon_frontier_strip w hwl hw,
    hne,hze,hwe⟩

/-- Each retained cut is bounded by a genuine complete hyperbolic line. -/
theorem cofiniteCut_exists_discLine (n:ℕ) :
    ∃L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,∀z:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈L.carrier ↔
      z.re=cofiniteCutValue n (Complex.normSq (z:ℂ)) := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-1/2) 1 (by norm_num)
  have ha:a∈cofiniteCutRegion:=cofiniteCutRegion_contains_left a (by
    change (-1/2:ℝ)< -2*cofiniteCutEpsilon;norm_num [cofiniteCutEpsilon])
  have hal:inner ℝ (cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))<
      cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n):=
    (cofiniteCut_klein_lt _ _ a).mp (ha n)
  have hbr:cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n)<
      inner ℝ (cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I)) := by
    have hneg:=cofiniteCutValue_neg_on_annulus n 1 (by
      have h1:16≤cofiniteCutSeam (n+1):=by
        dsimp [cofiniteCutSeam];push_cast;nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      linarith)
    have hgt:cofiniteCutValue n (Complex.normSq (UpperHalfPlane.I:ℂ))<UpperHalfPlane.I.re:=by
      simpa using hneg
    have h:= (cofiniteCut_klein_gt _ _ UpperHalfPlane.I).mp hgt
    rw [inner_neg_left] at h
    exact neg_lt_neg_iff.mp h
  obtain ⟨L,hL⟩:=exists_discLine_of_straddling_klein_cut _ _
    (cofiniteCutNormal_ne_zero _ _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I) hal hbr
  exact ⟨L,fun z=>(hL (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)).trans (cofiniteCut_klein_eq
    _ _ z).symm⟩


/-- A component of a genuine disc-line complement has an oriented, nonzero affine equation. -/
theorem cofinite_oriented_disc_cut (L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (a:Complex.UnitDisc) (ha:a∉L.carrier) :
    ∃(m:ℂ)(t:ℝ),m≠0∧(∀z:Complex.UnitDisc,z∈L.carrier↔inner ℝ m
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)=t)∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane L a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt m t := by
  obtain ⟨m,t,hm,hL⟩:=L.exists_klein_linear_equation
  have hne:inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate a)≠t:=fun he=>ha ((hL a).mpr he)
  rcases lt_or_gt_of_ne hne with hl|hr
  · exact ⟨m,t,hm,hL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_discLine_lt L m t hL a hl⟩
  · have hLn (z:Complex.UnitDisc) : z∈L.carrier↔inner ℝ (-m) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)= -t:=by
      rw [inner_neg_left,neg_inj]
      exact hL z
    exact ⟨-m,-t,neg_ne_zero.mpr hm,hLn,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_discLine_lt L (-m) (-t) hLn a (by rw [inner_neg_left];linarith)⟩

/-- An interior point of each true flat edge forces any exact half-plane representation
    to retain that edge's complete line and its prescribed open side. -/
theorem cofinite_exact_halfplanes_essential {I:Type*} (a:ℍ) (ha:a∈cofinitePolygon)
    (L:I→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hD:∀z:ℍ,z∈cofinitePolygon↔∀j:I,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a))
    (n:ℕ) (hn:1≤n) :
    ∃j:I,(∀z:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(L j).carrier↔
      z.re=cofiniteCutValue n (Complex.normSq (z:ℂ)))∧
      (∀z:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)↔
        z.re<cofiniteCutValue n (Complex.normSq (z:ℂ))) := by
  classical
  have haN (j:I) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a∉(L j).carrier:=
    connectedComponentIn_subset (L j).carrierᶜ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      a) ((hD a).mp ha j)
  choose m t hm hline hopen using fun j=>cofinite_oriented_disc_cut (L
    j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a) (haN j)
  have hbound (j:I) : closure cofinitePolygon⊆
      {z:ℍ|inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t j}:=by
    apply closure_minimal _ (isClosed_le
      (continuous_const.inner _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous) continuous_const)
    intro z hz
    have hh:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a):=(hD z).mp hz j
    rw [hopen j] at hh
    exact hh.le
  obtain ⟨z,w,hz,hw,hzw,hze,hwe⟩:=cofinitePolygon_flat_pair n hn
  have hC:Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' closure cofinitePolygon):=by
    have h:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mp
        cofinitePolygon_hConvex.closure)
    change Convex ℝ ((fun z:ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) '' closure cofinitePolygon)
    simpa only [image_image] using h
  obtain ⟨v,hvcl,hvK⟩:=hC.midpoint_mem
    (mem_image_of_mem _ (frontier_subset_closure hz))
    (mem_image_of_mem _ (frontier_subset_closure hw))
  have hmid (q:ℂ) : inner ℝ q (midpoint ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w))=
      (inner ℝ q (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)+inner ℝ q (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w))/2:=by
    rw [midpoint_eq_smul_add]
    simp only [inner_add_right,real_inner_smul_right,invOf_eq_inv]
    ring
  let N:=cofiniteCutNormal (cofiniteCutOffset n) (cofiniteCutSlope n)
  let T:=cofiniteCutThreshold (cofiniteCutOffset n) (cofiniteCutSlope n)
  have hzN:inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
    z)=T:=(cofiniteCut_klein_eq _ _ z).mp hze
  have hwN:inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
    w)=T:=(cofiniteCut_klein_eq _ _ w).mp hwe
  have hvN:inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate v)=T:=by rw [hvK,hmid,hzN,hwN];ring
  have hve:v.re=cofiniteCutValue n (Complex.normSq (v:ℂ)):=
    (cofiniteCut_klein_eq _ _ v).mpr hvN
  have hvnot:v∉cofinitePolygon:=by
    intro h
    have hlt:=h.1 n
    rw [hve] at hlt
    exact (lt_irrefl _) hlt
  have hnot:¬∀j:I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a):=
    fun h=>hvnot ((hD v).mpr h)
  push Not at hnot
  obtain ⟨j,hj⟩:=hnot
  have hvge:t j≤ inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate v):=by
    apply le_of_not_gt
    intro h
    apply hj
    rw [hopen j]
    exact h
  have hzle:inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t j:=
    hbound j (frontier_subset_closure hz)
  have hwle:inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t j:=
    hbound j (frontier_subset_closure hw)
  rw [hvK,hmid] at hvge
  have hzM:inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)=t j:=by linarith
  have hwM:inner ℝ (m j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t j:=by linarith
  have hEq (u:Complex.UnitDisc) : u∈(L
    j).carrier↔inner ℝ N (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate u)=T:=
    (hline j u).trans (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points (hm
      j)
      (cofiniteCutNormal_ne_zero _
        _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective.ne
        hzw) hzM hwM hzN hwN)
  have hOpen:_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L
    j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    a)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt N T:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_discLine_lt (L
      j) N T hEq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)
      ((cofiniteCut_klein_lt _ _ a).mp (ha.1 n))
  refine ⟨j,fun u=>(hEq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u)).trans
    (cofiniteCut_klein_eq _ _ u).symm,fun u=>?_⟩
  rw [hOpen]
  exact (cofiniteCut_klein_lt _ _ u).symm

/-- Infinitely many factors in every exact genuine half-plane representation omit the
    same native point. The assertion does not require a countability assumption. -/
theorem cofinite_exact_halfplanes_infinitely_exclude_i {I:Type*} (a:ℍ) (ha:a∈cofinitePolygon)
    (L:I→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hD:∀z:ℍ,z∈cofinitePolygon↔∀j:I,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)) :
    {j:I|_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)}.Infinite := by
  classical
  choose f hfeq hfopen using fun n:ℕ=>cofinite_exact_halfplanes_essential a ha L hD (n+1) (by omega)
  have hf_bad (n:ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∉
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L (f n)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a):=by
    intro hh
    have h:=(hfopen n UpperHalfPlane.I).mp hh
    exact cofiniteCut_excludes_i (n+1) h
  intro hfin
  let f':ℕ→{j:I|_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    UpperHalfPlane.I∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a)}:=
    fun n=>⟨f n,hf_bad n⟩
  have hinj:Function.Injective f':=by
    intro n m hnm
    have he:f n=f m:=congrArg Subtype.val hnm
    obtain ⟨z,w,_,_,hzw,hzn,hwn⟩:=cofinitePolygon_flat_pair (n+1) (by omega)
    have hzL:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(L (f m)).carrier:=he ▸ (hfeq n
      z).mpr hzn
    have hwL:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w∈(L (f m)).carrier:=he ▸ (hfeq n
      w).mpr hwn
    have hzm:=(hfeq m z).mp hzL
    have hwm:=(hfeq m w).mp hwL
    have hu:Complex.normSq (z:ℂ)≠Complex.normSq (w:ℂ):=
      fun h=>hzw (cofiniteCutLine_normSq_injective _ hzn hwn h)
    have hprod:(cofiniteCutSlope (n+1)-cofiniteCutSlope (m+1))*
        (Complex.normSq (z:ℂ)-Complex.normSq (w:ℂ))=0:=by
      dsimp only [cofiniteCutValue] at hzn hwn hzm hwm
      nlinarith
    have hslope:cofiniteCutSlope (n+1)=cofiniteCutSlope (m+1):=
      sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hu))
    have hsucc:=(strictAnti_nat_of_succ_lt cofiniteCutSlope_succ_lt).injective hslope
    omega
  let :=hfin.fintype
  exact (Finite.of_injective f' hinj).false


/-- The actual original polygon has locally finite true boundary sides. -/
theorem cofiniteOriginalPolygon_compact_sides_finite
    (K:Set infiniteSideData.cayleyData.domain.carrier) (hK:IsCompact K) :
    {S|IsFuchsianPolygonSide infiniteSideData.cayleyData cofiniteOriginalPolygon S∧
      (S∩K).Nonempty}.Finite :=
  cofiniteOriginalPolygon_convexPolygon.locallyFinite.compact_sides_finite K hK

/-- Every exact genuine half-plane representation of the actual original convex,
    locally finite fundamental polygon has infinitely many factors excluding one
    explicit compact singleton. -/
theorem cofiniteOriginalPolygon_bad_singleton {I:Type*}
    (a:infiniteSideData.cayleyData.domain.carrier) (ha:a∈cofiniteOriginalPolygon)
    (L:I→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hD:cofiniteOriginalPolygon=⋂j:I,{x|infiniteSideData.cayleyData.finiteCoordinate x∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L
        j) (infiniteSideData.cayleyData.finiteCoordinate a)}) :
    IsCompact ({infiniteSideData.cayleyCoordinate UpperHalfPlane.I}:
      Set infiniteSideData.cayleyData.domain.carrier)∧
    {j:I|¬({infiniteSideData.cayleyCoordinate UpperHalfPlane.I}:
      Set infiniteSideData.cayleyData.domain.carrier)⊆
      {x|infiniteSideData.cayleyData.finiteCoordinate x∈
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (infiniteSideData.cayleyData.finiteCoordinate a)}}.Infinite := by
  obtain ⟨a',rfl⟩:=infiniteSideData.cayleyCoordinate.surjective a
  have hmem (z:ℍ) : infiniteSideData.cayleyCoordinate z∈cofiniteOriginalPolygon↔
      z∈cofinitePolygon:=by
    constructor
    · rintro ⟨w,hw,he⟩
      exact infiniteSideData.cayleyCoordinate.injective he ▸ hw
    · exact fun hz=>mem_image_of_mem _ hz
  have ha':a'∈cofinitePolygon:=(hmem a').mp ha
  have hDN (z:ℍ) : z∈cofinitePolygon↔∀j:I,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a'):=by
    rw [←hmem z,hD,mem_iInter]
    simp only [mem_ofPred_eq,infiniteSideData.cayleyCoordinate_finite]
  have hi:=cofinite_exact_halfplanes_infinitely_exclude_i a' ha' L hDN
  refine ⟨isCompact_singleton,?_⟩
  simpa only [singleton_subset_iff,mem_ofPred_eq,infiniteSideData.cayleyCoordinate_finite] using hi

/-- The ambient compact/cofinite clause fails for this actual original convex
    locally finite Fuchsian fundamental polygon. -/
theorem cofiniteOriginalPolygon_not_compact_cofinite_halfplanes {I:Type*}
    (a:infiniteSideData.cayleyData.domain.carrier) (ha:a∈cofiniteOriginalPolygon)
    (L:I→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine)
    (hD:cofiniteOriginalPolygon=⋂j:I,{x|infiniteSideData.cayleyData.finiteCoordinate x∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L
        j) (infiniteSideData.cayleyData.finiteCoordinate a)}) :
    ¬∀(K:Set infiniteSideData.cayleyData.domain.carrier),IsCompact K→
      {j:I|¬K⊆{x|infiniteSideData.cayleyData.finiteCoordinate x∈
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L j) (infiniteSideData.cayleyData.finiteCoordinate a)}}.Finite := by
  intro h
  obtain ⟨hK,hi⟩:=cofiniteOriginalPolygon_bad_singleton a ha L hD
  exact hi (h _ hK)

/-- A concrete actual-group counterexample, including the genuine polygon hypothesis.
    No proposed compact/cofinite conclusion is an input hypothesis. -/
theorem section_9_3_compact_cofinite_counterexample :
    IsConvexFuchsianPolygon infiniteSideData.cayleyData cofiniteOriginalPolygon∧
    ∀(I:Type)(a:infiniteSideData.cayleyData.domain.carrier),a∈cofiniteOriginalPolygon→
      ∀L:I→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,
        cofiniteOriginalPolygon=⋂j:I,{x|infiniteSideData.cayleyData.finiteCoordinate x∈
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L
            j) (infiniteSideData.cayleyData.finiteCoordinate a)}→
        ¬∀(K:Set infiniteSideData.cayleyData.domain.carrier),IsCompact K→
          {j:I|¬K⊆{x|infiniteSideData.cayleyData.finiteCoordinate x∈
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.openDiscHalfPlane (L
              j) (infiniteSideData.cayleyData.finiteCoordinate a)}}.Finite :=
  ⟨cofiniteOriginalPolygon_convexPolygon,fun _ a ha L hD=>
    cofiniteOriginalPolygon_not_compact_cofinite_halfplanes a ha L hD⟩

end LowDimensionalTopology.Geometry.Fuchsian
