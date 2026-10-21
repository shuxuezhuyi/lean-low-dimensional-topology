/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleFundamentalDomains
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeDihedralChambers
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCosineRule
public import Mathlib.Topology.Separation.Connected
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeClosedDirichletCover
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
/-!
# The genuine sharp three-side funnel polygon

The literal circle region is proved equal to the whole-group Dirichlet domain.
Its three actual sides and the original side pairings, local corner interiors,
and forward-tangent angles are derived from the specified transformations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Pointwise UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

local instance funnelKernelEvaluationAction {X : Type*} [MetricSpace X] : MulAction (X≃ᵢX) X where
  smul g x:=g x
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

/-- Strict metric Voronoi cells are wandering for their actual isometry subgroup. -/
theorem strict_isometry_dirichlet_wandering {X : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (w : X) (g : X ≃ᵢ X) (hg : g∈H) (hne : g≠1) :
    Disjoint (g • {z | ∀h∈H,h≠1→dist z w<dist z (h w)})
      {z | ∀h∈H,h≠1→dist z w<dist z (h w)} := by
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hgz
  have h1:=hz g⁻¹ (H.inv_mem hg) (inv_ne_one.mpr hne)
  have h2:=hgz g hg hne
  have he : dist z (g⁻¹ w)=dist (g z) w := by
    simpa using (g.dist_eq z (g⁻¹ w)).symm
  rw [he] at h1
  change dist (g z) w<dist (g z) (g w) at h2
  rw [g.dist_eq] at h2
  exact (h1.trans h2).false

/-- The strict cell of a genuine element of order three needs exactly its two nonidentity powers. -/
theorem order_three_strict_dirichlet_iff {X : Type*} [MetricSpace X]
    (g : X≃ᵢX) (hg : orderOf g=3) (w z : X) :
    (∀h∈Subgroup.zpowers g,h≠1→dist z w<dist z (h w)) ↔
      dist z w<dist z (g w) ∧ dist z w<dist z ((g^2) w) := by
  have hg1 : g≠1 := by intro he;rw [he,orderOf_one] at hg;omega
  have hg2 : g^2≠1 := by
    intro he
    have hd:=orderOf_dvd_of_pow_eq_one he
    rw [hg] at hd
    norm_num at hd
  constructor
  · intro h
    exact ⟨h g (Subgroup.mem_zpowers _) hg1,h (g^2) ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers _) 2) hg2⟩
  · rintro ⟨h1,h2⟩ h hh hh1
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hh
    have hp : g^(n%3)=h := by simpa only [hg,Nat.cast_ofNat] using (zpow_mod_orderOf g n).trans hn
    have hem : 0≤n%3 ∧ n%3<3:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
    have hc : n%3=0 ∨ n%3=1 ∨ n%3=2:=by omega
    rcases hc with he|he|he
    · rw [he,zpow_zero] at hp
      exact False.elim (hh1 hp.symm)
    · rw [he,zpow_one] at hp
      rwa [←hp]
    · rw [he,show (2:ℤ)=(2:ℕ) by norm_num,zpow_natCast] at hp
      rwa [←hp]

/-- Two genuine packing domains whose union is the whole space give a common wandering set. -/
theorem two_packing_domains_wandering {X : Type*} [MetricSpace X]
    (A B : Subgroup (X ≃ᵢ X)) (U V : Set X)
    (hU : ∀g∈A,g≠1→Disjoint (g • U) U)
    (hV : ∀g∈B,g≠1→Disjoint (g • V) V)
    (hcover : U∪V=univ) (g : X ≃ᵢ X) (hg : g∈A⊔B) (hne : g≠1) :
    Disjoint (g • (U∩V)) (U∩V) := by
  have hu (z : X) : z∈U ∨ z∈V := by
    change z∈U∪V
    rw [hcover]
    trivial
  apply two_pingPong_wandering A B Uᶜ Vᶜ (U∩V) ?_ ?_ ?_ ?_ ?_ ?_ g hg hne
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (hU f hf hf1) ⟨x,(hu x).resolve_right hx,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (hV f hf hf1) ⟨x,(hu x).resolve_left hx,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (hU f hf hf1) ⟨x,hx.1,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (hV f hf hf1) ⟨x,hx.2,rfl⟩ hfx
  · exact disjoint_left.mpr (fun _ hn hx=>hn hx.1)
  · exact disjoint_left.mpr (fun _ hn hx=>hn hx.2)

/-- One mirror extends a subgroup by its actual two cosets. -/
def mirrorSubgroupExtension {G : Type*} [Group G] (H : Subgroup G) (a : G)
    (ha : a*a=1) (hconj : ∀g∈H,a*g*a∈H) : Subgroup G where
  carrier:={g | g∈H ∨ g*a∈H}
  one_mem':=Or.inl H.one_mem
  mul_mem':=by
    intro g h hg hh
    rcases hg with hg|hg <;> rcases hh with hh|hh
    · exact Or.inl (H.mul_mem hg hh)
    · exact Or.inr (by simpa only [mul_assoc] using H.mul_mem hg hh)
    · exact Or.inr (by
        have he : g*h*a=(g*a)*(a*h*a) := by simp only [mul_assoc,←mul_assoc a a,ha,one_mul]
        rw [he]
        exact H.mul_mem hg (hconj h hh))
    · exact Or.inl (by
        have he : g*h=(g*a)*(a*(h*a)*a) := by simp only [mul_assoc,←mul_assoc a a,ha,one_mul,mul_one]
        rw [he]
        exact H.mul_mem hg (hconj (h*a) hh))
  inv_mem':=by
    intro g hg
    rcases hg with hg|hg
    · exact Or.inl (H.inv_mem hg)
    · right
      have hai : a⁻¹=a := (mul_eq_one_iff_eq_inv.mp ha).symm
      have he : g⁻¹*a=a*(g*a)⁻¹*a := by simp only [mul_inv_rev,hai,←mul_assoc,ha,one_mul]
      rw [he]
      exact hconj _ (H.inv_mem hg)

/-- Cutting a wandering mirror-invariant region yields a chamber wandering under both cosets. -/
theorem mirror_cut_wandering {X : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (a : X ≃ᵢ X) (ha : a*a=1)
    (hconj : ∀g∈H,a*g*a∈H) (W C : Set X) (hCW : C⊆W) (haC : a • C⊆W)
    (hcut : Disjoint (a • C) C)
    (hW : ∀g∈H,g≠1→Disjoint (g • W) W)
    (g : X ≃ᵢ X) (hg : g∈mirrorSubgroupExtension H a ha hconj) (hne : g≠1) :
    Disjoint (g • C) C := by
  rcases hg with hg|hg
  · exact (hW g hg hne).mono (smul_set_subset_smul_set_iff.mpr hCW) hCW
  · by_cases he : g*a=1
    · have hga : g=a := (mul_eq_one_iff_eq_inv.mp he).trans
        (mul_eq_one_iff_eq_inv.mp ha).symm
      simpa only [hga] using hcut
    · apply (hW (g*a) hg he).mono ?_ hCW
      rintro _ ⟨x,hx,rfl⟩
      refine ⟨a x,haC ⟨x,hx,rfl⟩,?_⟩
      change g (a (a x))=g x
      have heaa:=congrArg (fun f : X≃ᵢX=>f x) ha
      change a (a x)=x at heaa
      exact congrArg g heaa

/-- Doubling one genuine chamber across a mirror outside the conformal subgroup gives a wandering union. -/
theorem mirror_double_wandering {X : Type*} [MetricSpace X]
    (H K : Subgroup (X ≃ᵢ X)) (hHK : H≤K) (b : X≃ᵢX) (hb : b*b=1)
    (hbK : b∈K) (hbH : b∉H) (C : Set X)
    (hC : ∀g∈K,g≠1→Disjoint (g • C) C)
    (g : X≃ᵢX) (hg : g∈H) (hne : g≠1) :
    Disjoint (g • (C∪b • C)) (C∪b • C) := by
  have hbi : b⁻¹=b := (mul_eq_one_iff_eq_inv.mp hb).symm
  have hbb (x : X) : b (b x)=x := congrArg (fun f : X≃ᵢX=>f x) hb
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hy
  rcases hx with hx|⟨x,hx,rfl⟩ <;> rcases hy with hy|⟨y,hy,he⟩
  · exact disjoint_left.mp (hC g (hHK hg) hne) ⟨x,hx,rfl⟩ hy
  · have hbg : b*g≠1 := by
      intro he1
      have hgb : g=b := by
        calc
          g=b*(b*g) := by rw [←mul_assoc,hb,one_mul]
          _=b := by rw [he1,mul_one]
      exact hbH (hgb ▸ hg)
    apply disjoint_left.mp (hC (b*g) (K.mul_mem hbK (hHK hg)) hbg) ⟨x,hx,rfl⟩
    change b y=g x at he
    have he' : y=(b*g) x := by
      change y=b (g x)
      simpa only [hbb] using congrArg b he
    change (b*g) x∈C
    rw [←he']
    exact hy
  · have hgb : g*b≠1 := by
      intro he1
      have hgb : g=b := (mul_eq_one_iff_eq_inv.mp he1).trans hbi
      exact hbH (hgb ▸ hg)
    exact disjoint_left.mp (hC (g*b) (K.mul_mem (hHK hg) hbK) hgb) ⟨x,hx,rfl⟩ hy
  · have hbg : b*g*b≠1 := by
      intro he1
      apply hne
      calc
        g=b*(b*g*b)*b := by
          symm
          calc
            b*(b*g*b)*b=(b*b)*g*(b*b) := by group
            _=g := by rw [hb,one_mul,mul_one]
        _=1 := by rw [he1,mul_one,hb]
    apply disjoint_left.mp (hC (b*g*b) (K.mul_mem (K.mul_mem hbK (hHK hg)) hbK) hbg) ⟨x,hx,rfl⟩
    change b y=g (b x) at he
    have he' : y=(b*g*b) x := by
      change y=b (g (b x))
      simpa only [hbb] using congrArg b he
    change (b*g*b) x∈C
    rw [←he']
    exact hy

/-- A wandering open set remains wandering after passing to any open subset of its closure. -/
theorem open_closure_wandering {X : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (S D : Set X) (hS : IsOpen S) (hD : IsOpen D)
    (hDS : D⊆closure S) (hpack : ∀g∈H,g≠1→Disjoint (g • S) S)
    (g : X≃ᵢX) (hg : g∈H) (hne : g≠1) : Disjoint (g • D) D := by
  have h : Disjoint (g • S) (closure S):=(hpack g hg hne).closure_right
    (g.toHomeomorph.isOpenMap _ hS)
  have h' : Disjoint (g • S) D:=h.mono_right hDS
  have h'' : Disjoint (closure (g • S)) D:=h'.closure_left hD
  apply h''.mono_left
  calc
    g • D⊆g • closure S:=smul_set_subset_smul_set_iff.mpr hDS
    _=closure (g • S) := g.toHomeomorph.image_closure S

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The finite order-three corner of the literal sharp funnel region. -/
def sharpFunnelVertex : ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (5/12) (Real.sqrt 3/4) (by positivity)

def sharpFunnelRadius : ℝ := Real.sqrt 13/6

def sharpFunnelCenter : ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.sqrt 13/3) (by positivity)

/-- The original open three-geodesic region, expressed by its literal squared circle equations. -/
def sharpFunnelDomain : Set ℍ := {z | 13/36<Complex.normSq (z:ℂ) ∧
  Complex.normSq (z:ℂ)<52/9 ∧ 13/4<Complex.normSq ((z:ℂ)-(13/6:ℂ))}

def sharpFunnelClosedDomain : Set ℍ := {z | 13/36≤Complex.normSq (z:ℂ) ∧
  Complex.normSq (z:ℂ)≤52/9 ∧ 13/4≤Complex.normSq ((z:ℂ)-(13/6:ℂ))}

theorem sharpFunnelVertex_normSq : Complex.normSq (sharpFunnelVertex:ℂ)=13/36 := by
  norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

theorem sharpFunnelVertex_top_circle :
    Complex.normSq ((sharpFunnelVertex:ℂ)-(13/6:ℂ))=13/4 := by
  norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

theorem sharpCollarD_coe (z : ℍ) : ((sharpCollarD • z:ℍ):ℂ)=4*(z:ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [sharpCollarD]
  ring

theorem sharpFunnelVertex_dilation_normSq :
    Complex.normSq ((sharpCollarD • sharpFunnelVertex:ℍ):ℂ)=52/9 := by
  rw [sharpCollarD_coe,Complex.normSq_mul,sharpFunnelVertex_normSq]
  norm_num

theorem sharpFunnelVertex_dilation_top_circle :
    Complex.normSq (((sharpCollarD • sharpFunnelVertex:ℍ):ℂ)-(13/6:ℂ))=13/4 := by
  rw [sharpCollarD_coe]
  norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

theorem sharpFunnelVertex_halfturn :
    sharpCollarF • sharpFunnelVertex=sharpCollarD • sharpFunnelVertex := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,sharpCollarD_coe]
  have hd:=UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF) sharpFunnelVertex
  apply (div_eq_iff hd).mpr
  norm_num [sharpCollarF,sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.denom,
    Matrix.of_apply]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  all_goals nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

theorem sharpFunnelCenter_mem : sharpFunnelCenter∈sharpFunnelDomain := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
  norm_num [sharpFunnelDomain,sharpFunnelCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  constructor
  · nlinarith only [hs]
  · constructor <;> nlinarith only [hs]

/-- Actual distance comparison with two finite coordinate points, with no angle data supplied. -/
theorem metricProbe_dist_lt_iff (a b c d : ℝ) (hb : 0<b) (hd : 0<d) (z : ℍ) :
    dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe a b
      hb)<dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c d hd) ↔
      0<b*(Complex.normSq (z:ℂ)-2*c*z.re+c^2+d^2)-
        d*(Complex.normSq (z:ℂ)-2*a*z.re+a^2+b^2) := by
  have hc : dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe a b
    hb)<dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c d hd) ↔
      Real.cosh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe a b hb))<Real.cosh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c d hd)) := by
    rw [Real.cosh_lt_cosh,abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [hc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cosh_dist_norm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cosh_dist_norm,←Complex.normSq_eq_norm_sq,
    ←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  change (z.re*z.re+z.im*z.im+(a*a+b*b)-2*z.re*a)/(2*z.im*b)<
    (z.re*z.re+z.im*z.im+(c*c+d*d)-2*z.re*c)/(2*z.im*d) ↔ _
  simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  rw [div_lt_div_iff₀ (by positivity : 0<2*z.im*b) (by positivity : 0<2*z.im*d)]
  constructor <;> intro h
  · have hh : 0<2*z.im*(b*(z.re^2+z.im^2-2*c*z.re+c^2+d^2)-
        d*(z.re^2+z.im^2-2*a*z.re+a^2+b^2)) := by nlinarith only [h]
    simpa only [pow_two] using (mul_pos_iff_of_pos_left (by positivity : 0<2*z.im)).mp hh
  · have hh:=mul_pos (by positivity : 0<2*z.im) h
    nlinarith only [hh]

/-- The order-two factor center of the sharp funnel. -/
def sharpFunnelHalfTurnCenter : ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (2/3) 1 (by norm_num)

def sharpFunnelCyclicSector : Set ℍ := {z | 13/36<Complex.normSq (z:ℂ) ∧
  0<Complex.normSq (z:ℂ)-(13/12)*z.re+13/144}

theorem sharpFunnelR_center_image :
    (sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (17/30) (1/5) (by norm_num) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hd:=UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ (sharpCollarF*sharpCollarD)) sharpFunnelHalfTurnCenter
  apply (div_eq_iff hd).mpr
  norm_num [sharpCollarF,sharpCollarD,sharpFunnelHalfTurnCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,
    UpperHalfPlane.denom,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]

theorem sharpFunnelR_square_center_image :
    (sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (1/6) (1/4) (by norm_num) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hd:=UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ ((sharpCollarF*sharpCollarD)^2)) sharpFunnelHalfTurnCenter
  apply (div_eq_iff hd).mpr
  norm_num [sharpCollarF,sharpCollarD,sharpFunnelHalfTurnCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,
    UpperHalfPlane.denom,pow_two,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]

theorem sharpFunnelSector_dist_comparisons (z : ℍ) : z∈sharpFunnelCyclicSector ↔
    dist z sharpFunnelHalfTurnCenter<dist z ((sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter) ∧
    dist z sharpFunnelHalfTurnCenter<dist z ((sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter) := by
  rw [sharpFunnelR_center_image,sharpFunnelR_square_center_image]
  change _ ↔ dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _
    _)<_ ∧ dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _ _)<_
  rw [metricProbe_dist_lt_iff,metricProbe_dist_lt_iff]
  change (13/36<Complex.normSq (z:ℂ) ∧ 0<Complex.normSq (z:ℂ)-(13/12)*z.re+13/144) ↔ _
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith only [h1,h2]

theorem sharpFunnelSector_contains_outer (z : ℍ) (hz : 13/9≤Complex.normSq (z:ℂ)) :
    z∈sharpFunnelCyclicSector := by
  have hn : z.re^2≤Complex.normSq (z:ℂ) := by
    rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    nlinarith only [sq_nonneg z.im]
  constructor
  · linarith only [hz]
  · by_contra hf
    have hf' : Complex.normSq (z:ℂ)-(13/12)*z.re+13/144≤0:=le_of_not_gt hf
    nlinarith only [hf',hz,hn,sq_nonneg (z.re-13/12)]


/-- The order-two generator genuinely interchanges the two sides of the middle circle. -/
theorem sharpFunnelF_norm_relation (z : ℍ) :
    (Complex.normSq ((sharpCollarF • z:ℍ):ℂ)-13/9)*
      Complex.normSq ((z:ℂ)-(2/3:ℂ))=13/9-Complex.normSq (z:ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,Complex.normSq_div]
  change (Complex.normSq (((2/3:ℝ):ℂ)*(z:ℂ)+((-13/9:ℝ):ℂ))/
    Complex.normSq (((1:ℝ):ℂ)*(z:ℂ)+((-2/3:ℝ):ℂ))-13/9)*
    Complex.normSq ((z:ℂ)-(2/3:ℂ))=13/9-Complex.normSq (z:ℂ)
  have he : (((1:ℝ):ℂ)*(z:ℂ)+((-2/3:ℝ):ℂ))=(z:ℂ)-(2/3:ℂ) := by push_cast;ring
  rw [he]
  have hd : Complex.normSq ((z:ℂ)-(2/3:ℂ))≠0 := by
    apply (Complex.normSq_pos.mpr _).ne'
    intro he0
    have hi := congrArg Complex.im he0
    norm_num at hi
    exact z.im_pos.ne' hi
  rw [sub_mul,div_mul_cancel₀ _ hd]
  norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring


/-- The three physical mirrors underlying the original funnel. -/
def sharpFunnelInnerLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine := .circle 0 (Real.sqrt 13/6) (by positivity)
def sharpFunnelMiddleLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine := .circle 0 (Real.sqrt 13/3) (by positivity)
def sharpFunnelTopLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine := .circle (13/6) (Real.sqrt 13/2) (by positivity)

def sharpFunnelTopMirror : ℍ≃ᵢℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry sharpFunnelTopLine
def sharpFunnelMiddleMirror : ℍ≃ᵢℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry sharpFunnelMiddleLine

theorem sharpFunnel_top_middle_product :
    sharpFunnelTopMirror*sharpFunnelMiddleMirror=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF := by
  rw [sharpFunnelTopMirror,sharpFunnelMiddleMirror,reflectionProductSL_native]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL sharpFunnelTopLine sharpFunnelMiddleLine= -sharpCollarF := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,sharpFunnelTopLine,sharpFunnelMiddleLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,
        sharpCollarF,Matrix.mul_apply,Fin.sum_univ_two,div_pow,div_mul_div_comm,←pow_two,hs]
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg]

theorem sharpFunnel_middle_inner_product :
    sharpFunnelMiddleMirror*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry sharpFunnelInnerLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD := by
  rw [sharpFunnelMiddleMirror,reflectionProductSL_native]
  congr 1
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,sharpFunnelInnerLine,sharpFunnelMiddleLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,
      sharpCollarD,Matrix.mul_apply,Fin.sum_univ_two,div_pow,div_mul_div_comm,←pow_two,hs]

theorem sharpFunnelTopMirror_sq : sharpFunnelTopMirror*sharpFunnelTopMirror=1 := by
  simpa only [sharpFunnelTopMirror,pow_two] using halfPlaneLineReflectionIsometry_sq sharpFunnelTopLine

theorem sharpFunnelMiddleMirror_sq : sharpFunnelMiddleMirror*sharpFunnelMiddleMirror=1 := by
  simpa only [sharpFunnelMiddleMirror,pow_two] using halfPlaneLineReflectionIsometry_sq sharpFunnelMiddleLine

/-- The actual Euclidean inversion formula with a shifted observation center. -/
theorem circleReflection_shifted_normSq_product (c r d : ℝ) (hr : 0<r) (z : ℍ) :
    Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection c r hr
      z:ℂ)-(d:ℂ))*Complex.normSq ((z:ℂ)-(c:ℂ))=
      (c-d)^2*Complex.normSq (z:ℂ)+2*(c-d)*(r^2-c^2+c*d)*z.re+(r^2-c^2+c*d)^2 := by
  have hp : (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection c r hr z:ℍ):ℂ)-(d:ℂ))*(conj
    (z:ℂ)-(c:ℂ))=
      ((c-d:ℝ):ℂ)*conj (z:ℂ)+((r^2-c^2+c*d:ℝ):ℂ) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
    field_simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.conj_sub_real_ne_zero c z]
    push_cast
    ring
  have hn:=congrArg Complex.normSq hp
  rw [Complex.normSq_mul] at hn
  have he : Complex.normSq (conj (z:ℂ)-(c:ℂ))=Complex.normSq ((z:ℂ)-(c:ℂ)) := by
    simpa only [map_sub,Complex.conj_ofReal] using Complex.normSq_conj ((z:ℂ)-(c:ℂ))
  rw [he] at hn
  rw [hn]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,zero_mul,add_zero]
  ring

theorem sharpFunnelTopMirror_middle_sign (z : ℍ) :
    (Complex.normSq (sharpFunnelTopMirror z:ℂ)-13/9)*Complex.normSq ((z:ℂ)-(13/6:ℂ))=
      (13/4)*(Complex.normSq (z:ℂ)-13/9) := by
  have h:=circleReflection_shifted_normSq_product (13/6) (Real.sqrt 13/2) 0 (by positivity) z
  change (Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (13/6) (Real.sqrt 13/2) _
    z:ℂ)-13/9)*_= _
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs] at h
  have he : Complex.normSq ((z:ℂ)-(13/6:ℂ))=
      Complex.normSq (z:ℂ)-(13/3)*z.re+169/36 := by
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  rw [he] at h ⊢
  nlinarith only [h]

theorem sharpFunnelTopMirror_top_sign (z : ℍ) :
    (Complex.normSq ((sharpFunnelTopMirror z:ℂ)-(13/6:ℂ))-13/4)*
      Complex.normSq ((z:ℂ)-(13/6:ℂ))=
        -(13/4)*(Complex.normSq ((z:ℂ)-(13/6:ℂ))-13/4) := by
  have h:=circleReflection_shifted_normSq_product (13/6) (Real.sqrt 13/2) (13/6) (by positivity) z
  change (Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (13/6) (Real.sqrt 13/2) _
    z:ℂ)-(13/6:ℂ))-13/4)*_= _
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs] at h
  nlinarith only [h]

theorem sharpFunnelMiddleMirror_norm_product (z : ℍ) :
    Complex.normSq (sharpFunnelMiddleMirror z:ℂ)*Complex.normSq (z:ℂ)=169/81 := by
  have h:=circleReflection_shifted_normSq_product 0 (Real.sqrt 13/3) 0 (by positivity) z
  change Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 (Real.sqrt 13/3) _
    z:ℂ)*_= _
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs] at h
  exact h


theorem sharpFunnelMiddleMirror_top_sign (z : ℍ) :
    (Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ))-13/4)*Complex.normSq (z:ℂ)=
      (13/9)*(Complex.normSq ((z:ℂ)-(13/6:ℂ))-13/4) := by
  have h:=circleReflection_shifted_normSq_product 0 (Real.sqrt 13/3) (13/6) (by positivity) z
  change (Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 (Real.sqrt 13/3) _
    z:ℂ)-(13/6:ℂ))-13/4)*_= _
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs] at h
  have he : Complex.normSq ((z:ℂ)-(13/6:ℂ))=
      Complex.normSq (z:ℂ)-(13/3)*z.re+169/36 := by
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  rw [he]
  nlinarith only [h]

theorem sharpFunnelTopMirror_center_fixed :
    sharpFunnelTopMirror sharpFunnelHalfTurnCenter=sharpFunnelHalfTurnCenter := by
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (13/6) (Real.sqrt 13/2) _
    sharpFunnelHalfTurnCenter:ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [sharpFunnelHalfTurnCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,div_pow,←Complex.ofReal_pow,hs]
  apply Complex.ext <;> norm_num [Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem sharpFunnelTopMirror_corner_images :
    sharpFunnelTopMirror ((sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter)=
      (sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter := by
  rw [sharpFunnelR_center_image,sharpFunnelR_square_center_image]
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (13/6) (Real.sqrt 13/2) _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _ _):ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,div_pow,←Complex.ofReal_pow,hs]
  apply Complex.ext <;> norm_num [Complex.div_re,Complex.div_im,Complex.normSq_apply]



/-- The exact two-factor native group of the original sharp example. -/
def sharpFunnelNativeGroup : Subgroup (ℍ≃ᵢℍ) :=
  Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)} : Set
      (ℍ≃ᵢℍ))

def sharpFunnelHalfTurnSector : Set ℍ := {z | Complex.normSq (z:ℂ)<13/9}
def sharpFunnelGap : Set ℍ := sharpFunnelHalfTurnSector∩sharpFunnelCyclicSector

theorem sharpFunnelF_native_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)=2 := by
  rw [←realSLMobius_order_eq_native]
  exact sharpCollarF_order

theorem sharpFunnelR_native_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD))=3 := by
  rw [←realSLMobius_order_eq_native]
  exact sharpCollarR_order

theorem sharpFunnelHalfTurnSector_packing (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)) (hne : g≠1) :
    Disjoint (g • sharpFunnelHalfTurnSector) sharpFunnelHalfTurnSector := by
  obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hg
  have hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)^(n%2)=g := by
    simpa only [sharpFunnelF_native_order,Nat.cast_ofNat] using (zpow_mod_orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF) n).trans hn
  have hem : 0≤n%2 ∧ n%2<2:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have hrem : n%2=1 := by
    have hc : n%2=0 ∨ n%2=1:=by omega
    rcases hc with hc|hc
    · rw [hc,zpow_zero] at hp
      exact False.elim (hne hp.symm)
    · exact hc
  rw [hrem,zpow_one] at hp
  rw [←hp]
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hFz
  change Complex.normSq (z:ℂ)<13/9 at hz
  change Complex.normSq ((sharpCollarF • z:ℍ):ℂ)<13/9 at hFz
  have h:=sharpFunnelF_norm_relation z
  have hm:=mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hFz.le)
    (Complex.normSq_nonneg ((z:ℂ)-(2/3:ℂ)))
  linarith only [h,hm,hz]

theorem sharpFunnelCyclicSector_dirichlet (z : ℍ) : z∈sharpFunnelCyclicSector ↔
    ∀g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)),g≠1→
      dist z sharpFunnelHalfTurnCenter<dist z (g sharpFunnelHalfTurnCenter) := by
  rw [order_three_strict_dirichlet_iff _ sharpFunnelR_native_order]
  rw [sharpFunnelSector_dist_comparisons]
  have hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD))^2=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry ((sharpCollarF*sharpCollarD)^2) :=
    (map_pow _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _ 2).symm
  rw [hp]
  rfl

theorem sharpFunnelCyclicSector_packing (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (sharpCollarF*sharpCollarD))) (hne : g≠1) :
    Disjoint (g • sharpFunnelCyclicSector) sharpFunnelCyclicSector := by
  have he : sharpFunnelCyclicSector={z | ∀g∈Subgroup.zpowers
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)),
      g≠1→dist z sharpFunnelHalfTurnCenter<dist z (g sharpFunnelHalfTurnCenter)} :=
    Set.ext sharpFunnelCyclicSector_dirichlet
  rw [he]
  exact strict_isometry_dirichlet_wandering _ _ g hg hne

theorem sharpFunnel_factor_sectors_cover : sharpFunnelHalfTurnSector∪sharpFunnelCyclicSector=univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : Complex.normSq (z:ℂ)<13/9
  · exact Or.inl hz
  · exact Or.inr (sharpFunnelSector_contains_outer z (le_of_not_gt hz))

theorem sharpFunnelGap_packing (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelNativeGroup) (hne : g≠1) :
    Disjoint (g • sharpFunnelGap) sharpFunnelGap := by
  have he : sharpFunnelNativeGroup=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    sharpCollarF)⊔
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)) := by
    rw [sharpFunnelNativeGroup,←Set.singleton_union,Subgroup.closure_union,
      ←Subgroup.zpowers_eq_closure,←Subgroup.zpowers_eq_closure]
  rw [he] at hg
  exact two_packing_domains_wandering _ _ _ _ sharpFunnelHalfTurnSector_packing
    sharpFunnelCyclicSector_packing sharpFunnel_factor_sectors_cover g hg hne

/-- The actual three-wall region is open in the native metric topology. -/
theorem sharpFunnelDomain_open : IsOpen sharpFunnelDomain := by
  have hn : Continuous (fun z : ℍ=>Complex.normSq (z:ℂ)):=Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe
  have ht : Continuous (fun z : ℍ=>Complex.normSq ((z:ℂ)-(13/6:ℂ))):=
    Complex.continuous_normSq.comp (UpperHalfPlane.continuous_coe.sub continuous_const)
  exact (isOpen_lt continuous_const hn).inter ((isOpen_lt hn continuous_const).inter (isOpen_lt continuous_const ht))

theorem sharpFunnelHalfTurnSector_open : IsOpen sharpFunnelHalfTurnSector :=
  isOpen_lt (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe) continuous_const

def sharpFunnelChamber : Set ℍ := sharpFunnelDomain∩sharpFunnelHalfTurnSector

theorem sharpFunnelChamber_subset_gap : sharpFunnelChamber⊆sharpFunnelGap := by
  rintro z ⟨hz,hzA⟩
  refine ⟨hzA,hz.1,?_⟩
  have he : Complex.normSq ((z:ℂ)-(13/6:ℂ))=Complex.normSq (z:ℂ)-(13/3)*z.re+169/36 := by
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  have ht:=hz.2.2
  rw [he] at ht
  change 0<Complex.normSq (z:ℂ)-(13/12)*z.re+13/144
  nlinarith only [ht,hz.1]

theorem sharpFunnelTopMirror_halfTurnSector (z : ℍ) :
    sharpFunnelTopMirror z∈sharpFunnelHalfTurnSector ↔ z∈sharpFunnelHalfTurnSector := by
  have hd : 0<Complex.normSq ((z:ℂ)-(13/6:ℂ)) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi:=congrArg Complex.im he
    norm_num at hi
    exact z.im_pos.ne' hi
  have h:=sharpFunnelTopMirror_middle_sign z
  change Complex.normSq (sharpFunnelTopMirror z:ℂ)<13/9 ↔ Complex.normSq (z:ℂ)<13/9
  constructor <;> intro hz
  · have hh:=mul_neg_of_neg_of_pos (sub_neg.mpr hz) hd
    nlinarith only [h,hh]
  · have hh : (Complex.normSq (sharpFunnelTopMirror z:ℂ)-13/9)*Complex.normSq ((z:ℂ)-(13/6:ℂ))<0:=by
      nlinarith only [h,hz]
    have hh' : (Complex.normSq (sharpFunnelTopMirror z:ℂ)-13/9)*Complex.normSq ((z:ℂ)-(13/6:ℂ))<0*Complex.normSq ((z:ℂ)-(13/6:ℂ)):=by simpa only [zero_mul] using hh
    exact sub_neg.mp ((mul_lt_mul_iff_left₀ hd).mp hh')

theorem sharpFunnelTopMirror_cyclicSector (z : ℍ) :
    sharpFunnelTopMirror z∈sharpFunnelCyclicSector ↔ z∈sharpFunnelCyclicSector := by
  have ha (x : ℍ) : sharpFunnelTopMirror (sharpFunnelTopMirror x)=x :=
    congrArg (fun f : ℍ≃ᵢℍ=>f x) sharpFunnelTopMirror_sq
  have hc : sharpFunnelTopMirror ((sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter)=
      (sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter := by
    rw [←sharpFunnelTopMirror_corner_images,ha]
  have h0 : dist (sharpFunnelTopMirror z) sharpFunnelHalfTurnCenter=dist z sharpFunnelHalfTurnCenter := by
    simpa only [sharpFunnelTopMirror_center_fixed] using sharpFunnelTopMirror.dist_eq z sharpFunnelHalfTurnCenter
  have h1 : dist (sharpFunnelTopMirror z) ((sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter)=
      dist z ((sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter) := by
    rw [←hc]
    exact sharpFunnelTopMirror.dist_eq z _
  have h2 : dist (sharpFunnelTopMirror z) ((sharpCollarF*sharpCollarD)^2 • sharpFunnelHalfTurnCenter)=
      dist z ((sharpCollarF*sharpCollarD) • sharpFunnelHalfTurnCenter) := by
    rw [←sharpFunnelTopMirror_corner_images]
    exact sharpFunnelTopMirror.dist_eq z _
  rw [sharpFunnelSector_dist_comparisons,sharpFunnelSector_dist_comparisons,h0,h1,h2,and_comm]

theorem sharpFunnelTopMirror_gap (z : ℍ) :
    sharpFunnelTopMirror z∈sharpFunnelGap ↔ z∈sharpFunnelGap :=
  and_congr (sharpFunnelTopMirror_halfTurnSector z) (sharpFunnelTopMirror_cyclicSector z)

theorem sharpFunnelChamber_top_disjoint : Disjoint (sharpFunnelTopMirror • sharpFunnelChamber) sharpFunnelChamber := by
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ haz
  change sharpFunnelTopMirror z∈sharpFunnelChamber at haz
  have h:=sharpFunnelTopMirror_top_sign z
  have hm:=mul_nonneg (sub_nonneg.mpr haz.1.2.2.le)
    (Complex.normSq_nonneg ((z:ℂ)-(13/6:ℂ)))
  nlinarith only [h,hm,hz.1.2.2]

theorem sharpFunnelTopMirror_conjugates_generators :
    sharpFunnelTopMirror*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*sharpFunnelTopMirror=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF ∧
    sharpFunnelTopMirror*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)*sharpFunnelTopMirror=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD))⁻¹ := by
  let a:=sharpFunnelTopMirror
  let b:=sharpFunnelMiddleMirror
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry sharpFunnelInnerLine
  have ha : a*a=1:=sharpFunnelTopMirror_sq
  have hb : b*b=1:=sharpFunnelMiddleMirror_sq
  have hab : a*b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF:=sharpFunnel_top_middle_product
  have hbc : b*c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD:=sharpFunnel_middle_inner_product
  have hai : a⁻¹=a:=(mul_eq_one_iff_eq_inv.mp ha).symm
  have hbi : b⁻¹=b:=(mul_eq_one_iff_eq_inv.mp hb).symm
  have hci : c⁻¹=c:=halfPlaneLineReflectionIsometry_inv sharpFunnelInnerLine
  have hF2 : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)=1:=by
    simpa only [←pow_two,sharpFunnelF_native_order] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)
  have hFi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    sharpCollarF)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF:=
    (mul_eq_one_iff_eq_inv.mp hF2).symm
  have hba : b*a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF := by
    rw [←hbi,←hai,←mul_inv_rev,hab,hFi]
  have hR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)=a*c := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_)=_
    rw [map_mul]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD=a*c
    rw [←hab,←hbc]
    calc (a*b)*(b*c)=a*((b*b)*c):=by group
         _=a*c:=by rw [hb,one_mul]
  constructor
  · change a*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF
    rw [←hab]
    calc a*(a*b)*a=b*a:=by rw [←mul_assoc a a b,ha,one_mul]
         _=a*b:=hba.trans hab.symm
  · change a*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)*a=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD))⁻¹
    rw [hR,mul_inv_rev,hai,hci,←mul_assoc a a c,ha,one_mul]

theorem sharpFunnelTopMirror_normalizes (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelNativeGroup) :
    sharpFunnelTopMirror*g*sharpFunnelTopMirror∈sharpFunnelNativeGroup := by
  let a:=sharpFunnelTopMirror
  have ha : a*a=1:=sharpFunnelTopMirror_sq
  have hai : a⁻¹=a:=(mul_eq_one_iff_eq_inv.mp ha).symm
  change g∈Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with he|he
    · rw [he,sharpFunnelTopMirror_conjugates_generators.1]
      exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp he,sharpFunnelTopMirror_conjugates_generators.2]
      exact sharpFunnelNativeGroup.inv_mem (Subgroup.subset_closure (by simp))
  | one =>
    change a*1*a∈sharpFunnelNativeGroup
    simpa only [mul_one,ha] using sharpFunnelNativeGroup.one_mem
  | mul g h _ _ hga hha =>
    have he : a*(g*h)*a=(a*g*a)*(a*h*a) := by
      calc a*(g*h)*a=a*g*(a*a)*h*a:=by rw [ha];group
           _=(a*g*a)*(a*h*a):=by group
    rw [show sharpFunnelTopMirror*(g*h)*sharpFunnelTopMirror=a*(g*h)*a from rfl,he]
    exact sharpFunnelNativeGroup.mul_mem hga hha
  | inv g _ hga =>
    have he : a*g⁻¹*a=(a*g*a)⁻¹ := by rw [mul_inv_rev,mul_inv_rev,hai];group
    rw [show sharpFunnelTopMirror*g⁻¹*sharpFunnelTopMirror=a*g⁻¹*a from rfl,he]
    exact sharpFunnelNativeGroup.inv_mem hga

def sharpFunnelReflectionExtension : Subgroup (ℍ≃ᵢℍ) :=
  mirrorSubgroupExtension sharpFunnelNativeGroup sharpFunnelTopMirror
    sharpFunnelTopMirror_sq sharpFunnelTopMirror_normalizes

theorem sharpFunnelChamber_wandering (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelReflectionExtension) (hne : g≠1) :
    Disjoint (g • sharpFunnelChamber) sharpFunnelChamber := by
  apply mirror_cut_wandering sharpFunnelNativeGroup sharpFunnelTopMirror
    sharpFunnelTopMirror_sq sharpFunnelTopMirror_normalizes sharpFunnelGap sharpFunnelChamber
    sharpFunnelChamber_subset_gap ?_ sharpFunnelChamber_top_disjoint sharpFunnelGap_packing g hg hne
  rintro _ ⟨z,hz,rfl⟩
  exact (sharpFunnelTopMirror_gap z).mpr (sharpFunnelChamber_subset_gap hz)

/-- The actual middle mirror preserves all three defining inequalities of the original region. -/
theorem sharpFunnelMiddleMirror_domain (z : ℍ) (hz : z∈sharpFunnelDomain) :
    sharpFunnelMiddleMirror z∈sharpFunnelDomain := by
  have hv : 0<Complex.normSq (z:ℂ):=Complex.normSq_pos.mpr z.ne_zero
  have hnorm:=sharpFunnelMiddleMirror_norm_product z
  have he : Complex.normSq (sharpFunnelMiddleMirror z:ℂ)=(169/81)/Complex.normSq (z:ℂ) :=
    (eq_div_iff hv.ne').mpr hnorm
  refine ⟨?_,?_,?_⟩
  · rw [he]
    apply (lt_div_iff₀ hv).mpr
    nlinarith only [hz.2.1]
  · rw [he]
    apply (div_lt_iff₀ hv).mpr
    nlinarith only [hz.1]
  · have h:=sharpFunnelMiddleMirror_top_sign z
    have hp : 0<(Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ))-13/4)*Complex.normSq (z:ℂ):=by
      nlinarith only [h,hz.2.2]
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hv).mp hp)

theorem sharpFunnelDomain_off_middle_subset_double (z : ℍ) (hz : z∈sharpFunnelDomain)
    (hne : Complex.normSq (z:ℂ)≠13/9) :
    z∈sharpFunnelChamber∪sharpFunnelMiddleMirror • sharpFunnelChamber := by
  rcases lt_or_gt_of_ne hne with hzlt|hzgt
  · exact Or.inl ⟨hz,hzlt⟩
  · right
    have hnorm:=sharpFunnelMiddleMirror_norm_product z
    have hv : 0<Complex.normSq (z:ℂ):=Complex.normSq_pos.mpr z.ne_zero
    have hlow : Complex.normSq (sharpFunnelMiddleMirror z:ℂ)<13/9 := by
      have he : Complex.normSq (sharpFunnelMiddleMirror z:ℂ)=(169/81)/Complex.normSq (z:ℂ) :=
        (eq_div_iff hv.ne').mpr hnorm
      rw [he]
      apply (div_lt_iff₀ hv).mpr
      nlinarith only [hzgt]
    refine ⟨sharpFunnelMiddleMirror z,⟨sharpFunnelMiddleMirror_domain z hz,hlow⟩,?_⟩
    exact congrArg (fun f : ℍ≃ᵢℍ=>f z) sharpFunnelMiddleMirror_sq

theorem sharpFunnelMiddleMirror_in_extension : sharpFunnelMiddleMirror∈sharpFunnelReflectionExtension := by
  right
  have hF:=sharpFunnel_top_middle_product
  have hFi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF := by
    have h2 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF=1:=by
      simpa only [←pow_two,sharpFunnelF_native_order] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)
    exact (mul_eq_one_iff_eq_inv.mp h2).symm
  have he : sharpFunnelMiddleMirror*sharpFunnelTopMirror=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF := by
    rw [←hFi,←hF,mul_inv_rev]
    rw [(mul_eq_one_iff_eq_inv.mp sharpFunnelTopMirror_sq).symm,
      (mul_eq_one_iff_eq_inv.mp sharpFunnelMiddleMirror_sq).symm]
  rw [he]
  exact Subgroup.subset_closure (by simp)

theorem sharpFunnelNativeGroup_conformal : sharpFunnelNativeGroup≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with he|he
  · exact ⟨sharpCollarF,he.symm⟩
  · exact ⟨sharpCollarF*sharpCollarD,(Set.mem_singleton_iff.mp he).symm⟩

theorem sharpFunnelMiddleMirror_not_nativeGroup : sharpFunnelMiddleMirror∉sharpFunnelNativeGroup := by
  intro h
  exact halfPlaneLineReflectionIsometry_not_conformal sharpFunnelMiddleLine
    (sharpFunnelNativeGroup_conformal h)

theorem sharpFunnelDoubleChamber_packing (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelNativeGroup) (hne : g≠1) :
    Disjoint (g • (sharpFunnelChamber∪sharpFunnelMiddleMirror • sharpFunnelChamber))
      (sharpFunnelChamber∪sharpFunnelMiddleMirror • sharpFunnelChamber) :=
  mirror_double_wandering sharpFunnelNativeGroup sharpFunnelReflectionExtension (fun _ hg=>Or.inl hg)
    sharpFunnelMiddleMirror sharpFunnelMiddleMirror_sq sharpFunnelMiddleMirror_in_extension
    sharpFunnelMiddleMirror_not_nativeGroup sharpFunnelChamber sharpFunnelChamber_wandering g hg hne

/-- Removing the real middle circle does not change the closure of the genuine open region. -/
theorem sharpFunnelDomain_subset_closure_double :
    sharpFunnelDomain⊆closure (sharpFunnelChamber∪sharpFunnelMiddleMirror • sharpFunnelChamber) := by
  have hDense : Dense (sharpFunnelMiddleLine.carrier)ᶜ := by
    rw [←interior_eq_empty_iff_dense_compl]
    have he : sharpFunnelMiddleLine.carrier=((↑) : ℍ→ℂ) ⁻¹' Metric.sphere 0 (Real.sqrt 13/3) := by
      ext x
      simp only [sharpFunnelMiddleLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier,Complex.ofReal_zero,sub_zero,mem_ofPred_eq,
        mem_preimage,Metric.mem_sphere,dist_zero_right]
    rw [he,←UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
      UpperHalfPlane.continuous_coe,interior_sphere',preimage_empty]
  intro z hz
  apply mem_closure_iff.mpr
  intro U hU hzU
  obtain ⟨x,hxL,hx⟩:=hDense.exists_mem_open (hU.inter sharpFunnelDomain_open) ⟨z,hzU,hz⟩
  refine ⟨x,hx.1,sharpFunnelDomain_off_middle_subset_double x hx.2 ?_⟩
  intro hnorm
  apply hxL
  change ‖(x:ℂ)-(0:ℂ)‖=Real.sqrt 13/3
  rw [sub_zero]
  have hn0 : 0≤‖(x:ℂ)‖:=norm_nonneg _
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  rw [Complex.normSq_eq_norm_sq] at hnorm
  nlinarith only [hnorm,hs,hn0,Real.sqrt_nonneg 13]

/-- Whole-group packing of the literal three-geodesic sharp funnel, including its middle-circle points. -/
theorem sharpFunnelDomain_packing (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelNativeGroup) (hne : g≠1) :
    Disjoint (g • sharpFunnelDomain) sharpFunnelDomain := by
  apply open_closure_wandering sharpFunnelNativeGroup
    (sharpFunnelChamber∪sharpFunnelMiddleMirror • sharpFunnelChamber) sharpFunnelDomain
    ?_ sharpFunnelDomain_open sharpFunnelDomain_subset_closure_double sharpFunnelDoubleChamber_packing g hg hne
  exact (sharpFunnelDomain_open.inter sharpFunnelHalfTurnSector_open).union
    (sharpFunnelMiddleMirror.toHomeomorph.isOpenMap _
      (sharpFunnelDomain_open.inter sharpFunnelHalfTurnSector_open))


/-- A common strict witness makes every weak affine-cut point a true limit of strict-cut points. -/
theorem affine_cuts_ball_weak_mem_closure {ι : Type*} (n : ι→ℂ) (t : ι→ℝ)
    (w x : ℂ) (hw : w∈Metric.ball 0 1) (hx : x∈Metric.ball 0 1)
    (hwc : ∀i,inner ℝ (n i) w<t i) (hxc : ∀i,inner ℝ (n i) x≤ t i) :
    x∈closure ({u : ℂ | ∀i,inner ℝ (n i) u<t i}∩Metric.ball 0 1) := by
  have hseg : openSegment ℝ x w⊆{u : ℂ | ∀i,inner ℝ (n i) u<t i}∩Metric.ball 0 1 := by
    rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    constructor
    · intro i
      rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
      calc
        a*inner ℝ (n i) x+b*inner ℝ (n i) w<a*t i+b*t i:=
          add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hxc i) ha.le)
            (mul_lt_mul_of_pos_left (hwc i) hb)
        _=t i:=by rw [←add_mul,hab,one_mul]
    · exact convex_ball (0:ℂ) 1 hx hw ha.le hb.le hab
  exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x w))

def sharpFunnelKleinNormals : Fin 3→ℂ := ![-49,61,⟨4,-39⟩]
def sharpFunnelKleinThresholds : Fin 3→ℝ := ![23,43,22]
def sharpFunnelKleinScales : Fin 3→ℝ := ![72,18,18]
def sharpFunnelSlacks (z : ℍ) : Fin 3→ℝ := ![Complex.normSq (z:ℂ)-13/36,
  52/9-Complex.normSq (z:ℂ),Complex.normSq ((z:ℂ)-(13/6:ℂ))-13/4]

theorem sharpFunnelKlein_slack (z : ℍ) (i : Fin 3) :
    (sharpFunnelKleinThresholds i-inner ℝ (sharpFunnelKleinNormals i)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
      (Complex.normSq (z:ℂ)+1)=sharpFunnelKleinScales i*sharpFunnelSlacks z i := by
  have hd : z.re^2+z.im^2+1≠0:=ne_of_gt (by positivity)
  fin_cases i <;>
    norm_num [sharpFunnelKleinThresholds,sharpFunnelKleinNormals,sharpFunnelKleinScales,sharpFunnelSlacks,
      _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  all_goals field_simp [hd];ring

theorem sharpFunnelSlack_pos_iff (z : ℍ) (i : Fin 3) :
    0<sharpFunnelSlacks z i ↔ inner ℝ (sharpFunnelKleinNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<sharpFunnelKleinThresholds i := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith only [Complex.normSq_nonneg (z:ℂ)]
  have hs : 0<sharpFunnelKleinScales i:=by fin_cases i <;> norm_num [sharpFunnelKleinScales]
  have h : (0<(sharpFunnelKleinThresholds i-inner ℝ (sharpFunnelKleinNormals i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
      (Complex.normSq (z:ℂ)+1)) ↔ 0<sharpFunnelKleinScales i*sharpFunnelSlacks z i := by
    rw [sharpFunnelKlein_slack]
  rw [mul_pos_iff_of_pos_right hd,mul_pos_iff_of_pos_left hs,sub_pos] at h
  exact h.symm

theorem sharpFunnelSlack_nonneg_iff (z : ℍ) (i : Fin 3) :
    0≤ sharpFunnelSlacks z i ↔ inner ℝ (sharpFunnelKleinNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤ sharpFunnelKleinThresholds i := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith only [Complex.normSq_nonneg (z:ℂ)]
  have hs : 0<sharpFunnelKleinScales i:=by fin_cases i <;> norm_num [sharpFunnelKleinScales]
  have h : (0≤(sharpFunnelKleinThresholds i-inner ℝ (sharpFunnelKleinNormals i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
      (Complex.normSq (z:ℂ)+1)) ↔ 0≤ sharpFunnelKleinScales i*sharpFunnelSlacks z i := by
    rw [sharpFunnelKlein_slack]
  rw [mul_nonneg_iff_of_pos_right hd,mul_nonneg_iff_of_pos_left hs,sub_nonneg] at h
  exact h.symm

theorem sharpFunnelDomain_klein (z : ℍ) : z∈sharpFunnelDomain ↔
    ∀i,inner ℝ (sharpFunnelKleinNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<sharpFunnelKleinThresholds i := by
  constructor
  · intro h i
    apply (sharpFunnelSlack_pos_iff z i).mp
    fin_cases i <;> norm_num [sharpFunnelSlacks] <;> linarith only [h.1,h.2.1,h.2.2]
  · intro h
    have h0:=(sharpFunnelSlack_pos_iff z 0).mpr (h 0)
    have h1:=(sharpFunnelSlack_pos_iff z 1).mpr (h 1)
    have h2:=(sharpFunnelSlack_pos_iff z 2).mpr (h 2)
    norm_num [sharpFunnelSlacks] at h0 h1 h2
    exact ⟨h0,h1,h2⟩

theorem sharpFunnelClosedDomain_klein (z : ℍ) : z∈sharpFunnelClosedDomain ↔
    ∀i,inner ℝ (sharpFunnelKleinNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤ sharpFunnelKleinThresholds i := by
  constructor
  · intro h i
    apply (sharpFunnelSlack_nonneg_iff z i).mp
    fin_cases i <;> norm_num [sharpFunnelSlacks] <;> linarith only [h.1,h.2.1,h.2.2]
  · intro h
    have h0:=(sharpFunnelSlack_nonneg_iff z 0).mpr (h 0)
    have h1:=(sharpFunnelSlack_nonneg_iff z 1).mpr (h 1)
    have h2:=(sharpFunnelSlack_nonneg_iff z 2).mpr (h 2)
    norm_num [sharpFunnelSlacks] at h0 h1 h2
    exact ⟨h0,h1,h2⟩

theorem sharpFunnelDomain_klein_image : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' sharpFunnelDomain=
    {u : ℂ | ∀i,inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i}∩Metric.ball 0 1 := by
  have he : sharpFunnelDomain=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate ⁻¹'
      {u : ℂ | ∀i,inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i} :=
    Set.ext sharpFunnelDomain_klein
  rw [he,image_preimage_eq_inter_range,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate]

theorem sharpFunnelDomain_closure : closure sharpFunnelDomain=sharpFunnelClosedDomain := by
  have hn : Continuous (fun z : ℍ=>Complex.normSq (z:ℂ)):=Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe
  have ht : Continuous (fun z : ℍ=>Complex.normSq ((z:ℂ)-(13/6:ℂ))):=
    Complex.continuous_normSq.comp (UpperHalfPlane.continuous_coe.sub continuous_const)
  have hclosed : IsClosed sharpFunnelClosedDomain:=
    (isClosed_le continuous_const hn).inter ((isClosed_le hn continuous_const).inter (isClosed_le continuous_const ht))
  apply subset_antisymm
  · apply closure_minimal (show sharpFunnelDomain⊆sharpFunnelClosedDomain from fun _
    h=>⟨h.1.le,h.2.1.le,h.2.2.le⟩) hclosed
  · intro z hz
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.closure_eq_preimage_closure_image,
      sharpFunnelDomain_klein_image]
    exact affine_cuts_ball_weak_mem_closure sharpFunnelKleinNormals sharpFunnelKleinThresholds
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
        sharpFunnelCenter) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ mem_range_self _)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ mem_range_self _)
      ((sharpFunnelDomain_klein _).mp sharpFunnelCenter_mem) ((sharpFunnelClosedDomain_klein z).mp hz)

theorem sharpFunnelDomain_isConnected : IsConnected sharpFunnelDomain := by
  have hC : Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' sharpFunnelDomain) := by
    rw [sharpFunnelDomain_klein_image]
    have he : {u : ℂ | ∀i,inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i}=
        ⋂i : Fin 3,{u : ℂ | inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i} := by ext u;simp
    rw [he]
    exact (convex_iInter (fun i=>convex_halfSpace_lt (innerSL ℝ (sharpFunnelKleinNormals i)).toLinearMap.isLinear
      _)).inter
      (convex_ball (0:ℂ) 1)
  exact ⟨⟨sharpFunnelCenter,sharpFunnelCenter_mem⟩,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.isInducing.isPreconnected_image.mp hC.isPreconnected⟩

/-- Packing at an actual open interior point proves discreteness in the existing native group topology. -/
theorem sharpFunnelNativeGroup_discrete : DiscreteTopology sharpFunnelNativeGroup := by
  let U : Set sharpFunnelNativeGroup:={g | g.val sharpFunnelCenter∈sharpFunnelDomain}
  have heval : Continuous (fun g : sharpFunnelNativeGroup=>g.val sharpFunnelCenter):=
    _root_.LowDimensionalTopology.Geometry.Polygon.native_poincare_continuous_evaluation.comp (continuous_subtype_val.prodMk continuous_const)
  have ho : IsOpen U:=sharpFunnelDomain_open.preimage heval
  have he : U={1} := by
    apply subset_antisymm
    · intro g hg
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      by_contra hne
      exact disjoint_left.mp (sharpFunnelDomain_packing g.val g.property hne)
        ⟨sharpFunnelCenter,sharpFunnelCenter_mem,rfl⟩ hg
    · exact Set.singleton_subset_iff.mpr sharpFunnelCenter_mem
  apply discreteTopology_of_isOpen_singleton_one
  rw [←he]
  exact ho

theorem metricProbe_dist_le_iff (a b c d : ℝ) (hb : 0<b) (hd : 0<d) (z : ℍ) :
    dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe a b
      hb)≤ dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c d hd) ↔
      0≤ b*(Complex.normSq (z:ℂ)-2*c*z.re+c^2+d^2)-
        d*(Complex.normSq (z:ℂ)-2*a*z.re+a^2+b^2) := by
  rw [←not_lt,metricProbe_dist_lt_iff]
  constructor <;> intro h <;> linarith only [h]

theorem sharpFunnelCenter_halfturn_image : sharpCollarF • sharpFunnelCenter=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (52/51) (3*Real.sqrt 13/17) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hd:=UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF) sharpFunnelCenter
  apply (div_eq_iff hd).mpr
  norm_num [sharpCollarF,sharpFunnelCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.denom]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  all_goals nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤13)]

theorem sharpFunnelCenter_dilation_image : sharpCollarD • sharpFunnelCenter=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (4*Real.sqrt 13/3) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [sharpCollarD_coe]
  norm_num [sharpFunnelCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem sharpFunnelCenter_inverse_dilation_image : sharpCollarD⁻¹ • sharpFunnelCenter=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.sqrt 13/12) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [sharpCollarD,sharpFunnelCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem sharpFunnelCenter_inner_comparison (z : ℍ)
    (h : dist z sharpFunnelCenter≤dist z (sharpCollarD⁻¹ • sharpFunnelCenter)) :
    13/36≤Complex.normSq (z:ℂ) := by
  rw [sharpFunnelCenter_inverse_dilation_image] at h
  change dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _
    _)≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _ _) at h
  rw [metricProbe_dist_le_iff] at h
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hp : 0≤(Real.sqrt 13/4)*(Complex.normSq (z:ℂ)-13/36) := by
    convert h using 1
    norm_num [div_pow,hs]
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity : 0<Real.sqrt 13/4)).mp hp)

theorem sharpFunnelCenter_outer_comparison (z : ℍ)
    (h : dist z sharpFunnelCenter≤dist z (sharpCollarD • sharpFunnelCenter)) :
    Complex.normSq (z:ℂ)≤52/9 := by
  rw [sharpFunnelCenter_dilation_image] at h
  change dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _
    _)≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _ _) at h
  rw [metricProbe_dist_le_iff] at h
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hp : 0≤Real.sqrt 13*(52/9-Complex.normSq (z:ℂ)) := by
    convert h using 1
    norm_num [div_pow,mul_pow,hs]
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity : 0<Real.sqrt 13)).mp hp)

theorem sharpFunnelCenter_top_comparison (z : ℍ)
    (h : dist z sharpFunnelCenter≤dist z (sharpCollarF • sharpFunnelCenter)) :
    13/4≤Complex.normSq ((z:ℂ)-(13/6:ℂ)) := by
  rw [sharpFunnelCenter_halfturn_image] at h
  change dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _
    _)≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe _ _ _) at h
  rw [metricProbe_dist_le_iff] at h
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hp : 0≤(8*Real.sqrt 13/51)*(Complex.normSq ((z:ℂ)-(13/6:ℂ))-13/4) := by
    convert h using 1
    norm_num [div_pow,mul_pow,hs,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity : 0<8*Real.sqrt 13/51)).mp hp)

theorem sharpFunnelNative_generators_mem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF∈sharpFunnelNativeGroup ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD∈sharpFunnelNativeGroup := by
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF∈sharpFunnelNativeGroup:=Subgroup.subset_closure (by simp)
  have hr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)∈sharpFunnelNativeGroup:=Subgroup.subset_closure (by simp)
  have h2 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF=1:=by
    simpa only [←pow_two,sharpFunnelF_native_order] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)
  refine ⟨hf,?_⟩
  have hm:=sharpFunnelNativeGroup.mul_mem hf hr
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD:=
    map_mul _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _ _
  rw [he,←mul_assoc,h2,one_mul] at hm
  exact hm

/-- Every genuine closed Dirichlet comparison implies the three original weak circle inequalities. -/
theorem sharpFunnel_closedDirichlet_subset :
    nativeClosedDirichlet sharpFunnelNativeGroup sharpFunnelCenter⊆sharpFunnelClosedDomain := by
  intro z hz
  exact ⟨sharpFunnelCenter_inner_comparison z
    (hz ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹,sharpFunnelNativeGroup.inv_mem
      sharpFunnelNative_generators_mem.2⟩),
    sharpFunnelCenter_outer_comparison z (hz ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarD,sharpFunnelNative_generators_mem.2⟩),
    sharpFunnelCenter_top_comparison z (hz ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarF,sharpFunnelNative_generators_mem.1⟩)⟩

/-- Actual closed-region orbit coverage, deduced from nearest points of the full group. -/
theorem sharpFunnelDomain_closure_meetsEveryOrbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit sharpFunnelNativeGroup ℍ (closure sharpFunnelDomain) := by
  have sharpFunnelNativeDiscrete : DiscreteTopology sharpFunnelNativeGroup:=sharpFunnelNativeGroup_discrete
  have hd:=nativeConformalSubgroup_discontinuous sharpFunnelNativeGroup sharpFunnelNativeGroup_conformal
  intro z
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit sharpFunnelNativeGroup hd sharpFunnelCenter z
  refine ⟨g,?_⟩
  rw [sharpFunnelDomain_closure]
  exact sharpFunnel_closedDirichlet_subset hg

def sharpFunnelOuterLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine := .circle 0 (2*Real.sqrt 13/3) (by positivity)

theorem circle_carrier_iff_normSq (c r : ℝ) (hr : 0<r) (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c r hr).carrier ↔ Complex.normSq ((z:ℂ)-(c:ℂ))=r^2 := by
  change ‖(z:ℂ)-(c:ℂ)‖=r ↔ _
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h;rw [h]
  · intro h;nlinarith only [h,norm_nonneg ((z:ℂ)-(c:ℂ)),hr]

theorem sharpFunnelDomain_frontier_subset : frontier sharpFunnelDomain⊆
    sharpFunnelInnerLine.carrier∪sharpFunnelOuterLine.carrier∪sharpFunnelTopLine.carrier := by
  intro z hz
  have h:=sharpFunnelDomain_open.frontier_eq ▸ hz
  have hweak : z∈sharpFunnelClosedDomain:=sharpFunnelDomain_closure ▸ h.1
  have hn : z∉sharpFunnelDomain:=h.2
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  by_cases hinner : 13/36<Complex.normSq (z:ℂ)
  · by_cases houter : Complex.normSq (z:ℂ)<52/9
    · have ht : Complex.normSq ((z:ℂ)-(13/6:ℂ))=13/4 := by
        exact le_antisymm (le_of_not_gt (fun ht=>hn ⟨hinner,houter,ht⟩)) hweak.2.2
      right
      change z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle _ _ _).carrier
      rw [circle_carrier_iff_normSq]
      norm_num [div_pow,hs]
      exact ht
    · left;right
      have he : Complex.normSq (z:ℂ)=52/9:=le_antisymm hweak.2.1 (le_of_not_gt houter)
      change z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle _ _ _).carrier
      rw [circle_carrier_iff_normSq]
      norm_num [div_pow,mul_pow,hs]
      exact he
  · left;left
    have he : Complex.normSq (z:ℂ)=13/36:=le_antisymm (le_of_not_gt hinner) hweak.1
    change z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle _ _ _).carrier
    rw [circle_carrier_iff_normSq]
    norm_num [div_pow,hs]
    exact he

theorem sharpFunnelDomain_frontier_volume_zero : MeasureTheory.volume (frontier sharpFunnelDomain)=0 := by
  exact MeasureTheory.measure_mono_null sharpFunnelDomain_frontier_subset
    (MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null sharpFunnelInnerLine.volume_zero sharpFunnelOuterLine.volume_zero)
      sharpFunnelTopLine.volume_zero)

theorem sharpFunnelDomain_orbit_unique (x y : ℍ) (hx : x∈sharpFunnelDomain) (hy : y∈sharpFunnelDomain)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection sharpFunnelNativeGroup ℍ x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection sharpFunnelNativeGroup ℍ y) : x=y := by
  obtain ⟨g,hg⟩:=(Quotient.exact he : MulAction.orbitRel sharpFunnelNativeGroup ℍ x y)
  by_cases h1 : g.val=1
  · simpa only [show g=1 from Subtype.ext h1,one_smul] using hg.symm
  · exact False.elim (disjoint_left.mp (sharpFunnelDomain_packing g.val g.property h1) ⟨y,hy,hg⟩ hx)

/-- The literal original three-geodesic region is a genuine fundamental domain for the entire generated group. -/
theorem sharpFunnelDomain_fundamental :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain sharpFunnelNativeGroup ℍ MeasureTheory.volume sharpFunnelDomain := by
  refine ⟨sharpFunnelDomain_open,sharpFunnelDomain_isConnected,?_,sharpFunnelDomain_frontier_volume_zero⟩
  exact exists_fundamentalSet_between _ _ subset_closure sharpFunnelDomain_closure_meetsEveryOrbit
    (fun x hx y hy he=>sharpFunnelDomain_orbit_unique x y hx hy he)

/-- Every native word has a genuine real determinant-one lift in the original actual Mobius group. -/
theorem sharpFunnelNative_actual_lift (g : ℍ≃ᵢℍ) (hg : g∈sharpFunnelNativeGroup) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A=g ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈sharpCollarGroup := by
  let K:=sharpCollarGroup.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
  have hsub : sharpFunnelNativeGroup≤K.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases Set.mem_insert_iff.mp hh with he|he
    · exact ⟨sharpCollarF,sharpCollar_generators_mem.1,he.symm⟩
    · refine ⟨sharpCollarF*sharpCollarD,?_,(Set.mem_singleton_iff.mp he).symm⟩
      exact Subgroup.subset_closure (by simp)
  obtain ⟨A,hA,he⟩:=hsub hg
  exact ⟨A,he,hA⟩

def sharpFunnelToMobius : sharpFunnelNativeGroup→*_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  nativeConformalSubgroupMobiusHom sharpFunnelNativeGroup sharpFunnelNativeGroup_conformal

theorem sharpFunnelToMobius_range : sharpFunnelToMobius.range=sharpCollarGroup := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    obtain ⟨A,hAn,hAH⟩:=sharpFunnelNative_actual_lift g.val g.property
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈sharpFunnelNativeGroup:=by rw [hAn];exact g.property
    have he : g=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hm⟩:=Subtype.ext hAn.symm
    rw [he]
    change nativeConformalSubgroupMobiusHom _ _ ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A,hm⟩∈sharpCollarGroup
    rw [nativeConformalSubgroupMobiusHom_matrix]
    exact hAH
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with he|he
    · refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarF,sharpFunnelNative_generators_mem.1⟩,?_⟩
      exact (nativeConformalSubgroupMobiusHom_matrix _ _ _ _).trans he.symm
    · have hr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD)∈sharpFunnelNativeGroup:=Subgroup.subset_closure (by simp)
      refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpCollarF*sharpCollarD),hr⟩,?_⟩
      exact (nativeConformalSubgroupMobiusHom_matrix _ _ _ _).trans (Set.mem_singleton_iff.mp he).symm

def sharpFunnelGroupEquiv : sharpFunnelNativeGroup≃*sharpCollarGroup := by
  let f:=sharpFunnelToMobius.codRestrict sharpCollarGroup (fun g=>by
    rw [←sharpFunnelToMobius_range]
    exact ⟨g,rfl⟩)
  apply MulEquiv.ofBijective f
  constructor
  · intro g h he
    exact (nativeConformalSubgroupMobiusHom_isometry sharpFunnelNativeGroup sharpFunnelNativeGroup_conformal).injective
      (congrArg Subtype.val he)
  · intro g
    have hg : g.val∈sharpFunnelToMobius.range:=by rw [sharpFunnelToMobius_range];exact g.property
    obtain ⟨h,hh⟩:=hg
    exact ⟨h,Subtype.ext hh⟩

theorem sharpFunnelGroupEquiv_val (g : sharpFunnelNativeGroup) :
    (sharpFunnelGroupEquiv g).val=sharpFunnelToMobius g := rfl

theorem sharpFunnelGroupEquiv_action (g : sharpFunnelNativeGroup) (z : ℍ) :
    letI :=sharpCollarHalfPlaneData.nativeAction
    sharpFunnelGroupEquiv g • z=g.val z := by
  let sharpFunnelOriginalAction:=sharpCollarHalfPlaneData.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←sharpCollarHalfPlaneData.nativeAction_boundary,sharpFunnelGroupEquiv_val]
  exact nativeConformalSubgroupMobiusHom_action sharpFunnelNativeGroup sharpFunnelNativeGroup_conformal g z

/-- The same literal region, with its genuine original sphere group and actual native area. -/
theorem sharpFunnelDomain_original_fundamental :
    letI :=sharpCollarHalfPlaneData.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain sharpCollarGroup ℍ MeasureTheory.volume sharpFunnelDomain := by
  let sharpFunnelOriginalAction:=sharpCollarHalfPlaneData.nativeAction
  have he (g : sharpCollarGroup) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z)=sharpFunnelGroupEquiv.symm g • (Homeomorph.refl ℍ) z := by
    change g • z=(sharpFunnelGroupEquiv.symm g).val z
    simpa only [MulEquiv.apply_symm_apply] using sharpFunnelGroupEquiv_action (sharpFunnelGroupEquiv.symm g) z
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage sharpFunnelGroupEquiv.symm (Homeomorph.refl ℍ) he
    sharpFunnelDomain_fundamental
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain sharpCollarGroup ℍ (MeasureTheory.Measure.map id MeasureTheory.volume) (id ⁻¹' sharpFunnelDomain) at h
  simpa only [MeasureTheory.Measure.map_id,preimage_id] using h


local instance sharpFunnelDiscSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance sharpFunnelDiscSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

abbrev sharpFunnelDiscData := sharpCollarHalfPlaneData.cayleyData

def sharpFunnelDiscGroupEquiv : sharpFunnelNativeGroup≃*
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius sharpCollarGroup :=
  sharpFunnelGroupEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius sharpCollarGroup)

def sharpFunnelDiscCoordinate : ℍ≃ₜsharpFunnelDiscData.domain.carrier :=
  sharpCollarHalfPlaneData.cayleyCoordinate

theorem sharpFunnelDiscCoordinate_equivariant (g : sharpFunnelNativeGroup) (z : ℍ) :
    sharpFunnelDiscCoordinate (g.val z)=sharpFunnelDiscGroupEquiv g • sharpFunnelDiscCoordinate z := by
  have h:=sharpCollarHalfPlaneData.cayleyCoordinate_equivariant (sharpFunnelGroupEquiv g) z
  rw [sharpFunnelGroupEquiv_action] at h
  exact h

theorem sharpFunnelDiscCoordinate_metric (z w : ℍ) :
    sharpFunnelDiscData.hyperbolicDist (sharpFunnelDiscCoordinate z) (sharpFunnelDiscCoordinate w)=dist z w := by
  have h (x : ℍ) : sharpFunnelDiscData.halfPlaneCoordinate (sharpFunnelDiscCoordinate x)=x := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm (sharpFunnelDiscData.finiteCoordinate
      (sharpCollarHalfPlaneData.cayleyCoordinate x))=x
    rw [sharpCollarHalfPlaneData.cayleyCoordinate_finite]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm_apply_apply x
  change dist (sharpFunnelDiscData.halfPlaneCoordinate (sharpFunnelDiscCoordinate z))
    (sharpFunnelDiscData.halfPlaneCoordinate (sharpFunnelDiscCoordinate w))=dist z w
  rw [h,h]

theorem sharpFunnelCenter_free (g : sharpFunnelNativeGroup) (hg : g.val sharpFunnelCenter=sharpFunnelCenter) : g=1 := by
  apply Subtype.ext
  by_contra hne
  exact disjoint_left.mp (sharpFunnelDomain_packing g.val g.property hne)
    ⟨sharpFunnelCenter,sharpFunnelCenter_mem,hg⟩ sharpFunnelCenter_mem

theorem sharpFunnelDiscCenter_free :
    IsDirichletCenter sharpFunnelDiscData (sharpFunnelDiscCoordinate sharpFunnelCenter) := by
  intro g hg
  obtain ⟨k,rfl⟩:=sharpFunnelDiscGroupEquiv.surjective g
  have hk : k.val sharpFunnelCenter=sharpFunnelCenter :=
    sharpFunnelDiscCoordinate.injective ((sharpFunnelDiscCoordinate_equivariant k sharpFunnelCenter).trans hg)
  rw [sharpFunnelCenter_free k hk,map_one]

theorem sharpFunnelDirichlet_preimage : sharpFunnelDiscCoordinate ⁻¹'
    dirichletDomain sharpFunnelDiscData (sharpFunnelDiscCoordinate sharpFunnelCenter)=
      nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter := by
  ext z
  constructor
  · intro hz g hg
    have hne : sharpFunnelDiscGroupEquiv g≠1:=fun he=>hg
      (sharpFunnelDiscGroupEquiv.injective (he.trans (map_one sharpFunnelDiscGroupEquiv).symm))
    have h:=hz (sharpFunnelDiscGroupEquiv g) hne
    change sharpFunnelDiscData.hyperbolicDist (sharpFunnelDiscCoordinate z) (sharpFunnelDiscCoordinate
      sharpFunnelCenter)<
      sharpFunnelDiscData.hyperbolicDist (sharpFunnelDiscCoordinate z) (sharpFunnelDiscGroupEquiv g •
        sharpFunnelDiscCoordinate sharpFunnelCenter) at h
    rw [←sharpFunnelDiscCoordinate_equivariant,sharpFunnelDiscCoordinate_metric,sharpFunnelDiscCoordinate_metric] at h
    exact h
  · intro hz g hg
    obtain ⟨k,rfl⟩:=sharpFunnelDiscGroupEquiv.surjective g
    have hk : k≠1:=by intro he;exact hg (he ▸ map_one sharpFunnelDiscGroupEquiv)
    have h:=hz k hk
    change sharpFunnelDiscData.hyperbolicDist (sharpFunnelDiscCoordinate z) (sharpFunnelDiscCoordinate
      sharpFunnelCenter)<
      sharpFunnelDiscData.hyperbolicDist (sharpFunnelDiscCoordinate z) (sharpFunnelDiscGroupEquiv k •
        sharpFunnelDiscCoordinate sharpFunnelCenter)
    rw [←sharpFunnelDiscCoordinate_equivariant,sharpFunnelDiscCoordinate_metric,sharpFunnelDiscCoordinate_metric]
    exact h

theorem sharpFunnelDiscCoordinate_area_pullback :
    MeasureTheory.Measure.map sharpFunnelDiscCoordinate.symm sharpFunnelDiscData.area=MeasureTheory.volume := by
  rw [←sharpCollarHalfPlaneData.cayleyCoordinate_area_map]
  change MeasureTheory.Measure.map sharpFunnelDiscCoordinate.symm (MeasureTheory.Measure.map sharpFunnelDiscCoordinate
    MeasureTheory.volume)=MeasureTheory.volume
  rw [MeasureTheory.Measure.map_map sharpFunnelDiscCoordinate.symm.continuous.measurable
    sharpFunnelDiscCoordinate.continuous.measurable]
  have he : (sharpFunnelDiscCoordinate.symm ∘ sharpFunnelDiscCoordinate : ℍ→ℍ)=id :=
    funext sharpFunnelDiscCoordinate.symm_apply_apply
  rw [he,MeasureTheory.Measure.map_id]

theorem sharpFunnelNativeDirichlet_fundamental : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain sharpFunnelNativeGroup ℍ MeasureTheory.volume
    (nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter) := by
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage sharpFunnelDiscGroupEquiv sharpFunnelDiscCoordinate
    sharpFunnelDiscCoordinate_equivariant
    (dirichletDomain_fundamental sharpFunnelDiscData _ sharpFunnelDiscCenter_free)
  rw [sharpFunnelDiscCoordinate_area_pullback,sharpFunnelDirichlet_preimage] at h
  exact h

theorem sharpFunnelNativeDirichlet_regular :
    interior (closure (nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter))=
      nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter := by
  rw [←sharpFunnelDirichlet_preimage,←sharpFunnelDiscCoordinate.preimage_closure,
    ←sharpFunnelDiscCoordinate.isOpenMap.preimage_interior_eq_interior_preimage sharpFunnelDiscCoordinate.continuous,
    (dirichletDomain_isConvexFuchsianPolygon sharpFunnelDiscData _ sharpFunnelDiscCenter_free).interior_closure]

theorem sharpFunnelDomain_regular : interior (closure sharpFunnelDomain)=sharpFunnelDomain := by
  apply interior_closure_eq_of_convex_open_embedding _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate
    sharpFunnelDomain sharpFunnelDomain_open ⟨sharpFunnelCenter,sharpFunnelCenter_mem⟩
  rw [sharpFunnelDomain_klein_image]
  have he : {u : ℂ | ∀i,inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i}=
      ⋂i : Fin 3,{u : ℂ | inner ℝ (sharpFunnelKleinNormals i) u<sharpFunnelKleinThresholds i} := by ext u;simp
  rw [he]
  exact (convex_iInter (fun i=>convex_halfSpace_lt (innerSL ℝ (sharpFunnelKleinNormals i)).toLinearMap.isLinear
    _)).inter
    (convex_ball (0:ℂ) 1)

theorem sharpFunnelNativeDirichlet_subset : nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter⊆sharpFunnelDomain := by
  rw [←sharpFunnelDomain_regular]
  apply sharpFunnelNativeDirichlet_fundamental.isOpen.subset_interior_iff.mpr
  rw [sharpFunnelDomain_closure]
  intro z hz
  apply sharpFunnel_closedDirichlet_subset
  intro g
  by_cases hg : g=1
  · subst g;exact le_rfl
  · exact (hz g hg).le

/-- The explicit three walls are proved equal to the genuine full-group Dirichlet domain. -/
theorem sharpFunnelDomain_eq_nativeDirichlet : sharpFunnelDomain=
    nativeDirichletDomain sharpFunnelNativeGroup sharpFunnelCenter := by
  apply subset_antisymm ?_ sharpFunnelNativeDirichlet_subset
  rw [←sharpFunnelNativeDirichlet_regular]
  apply sharpFunnelDomain_open.subset_interior_iff.mpr
  intro x hx
  obtain ⟨g,y,hy,hgy⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_covering sharpFunnelNativeGroup ℍ sharpFunnelNativeDirichlet_fundamental x
  by_cases hg : g.val=1
  · have he : y=x:=by simpa only [show g=1 from Subtype.ext hg,one_smul] using hgy
    rwa [←he]
  · have hpack:=(sharpFunnelDomain_packing g.val g.property hg).closure_left sharpFunnelDomain_open
    apply False.elim (disjoint_left.mp hpack ?_ hx)
    change x∈closure (g.val.toHomeomorph '' sharpFunnelDomain)
    rw [←g.val.toHomeomorph.image_closure]
    exact ⟨y,closure_mono sharpFunnelNativeDirichlet_subset hy,hgy⟩

/-- The true whole-group Dirichlet polygon, with no omitted compact-tile local-finiteness requirement. -/
theorem sharpFunnelDomain_original_polygon : IsConvexFuchsianPolygon sharpFunnelDiscData
    (sharpFunnelDiscCoordinate '' sharpFunnelDomain) := by
  have he : sharpFunnelDiscCoordinate '' sharpFunnelDomain=
      dirichletDomain sharpFunnelDiscData (sharpFunnelDiscCoordinate sharpFunnelCenter) := by
    rw [sharpFunnelDomain_eq_nativeDirichlet,←sharpFunnelDirichlet_preimage]
    exact sharpFunnelDiscCoordinate.surjective.image_preimage _
  rw [he]
  exact dirichletDomain_isConvexFuchsianPolygon sharpFunnelDiscData _ sharpFunnelDiscCenter_free


def sharpFunnelSideLine : Fin 3→_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine := ![sharpFunnelInnerLine,sharpFunnelOuterLine,sharpFunnelTopLine]
def sharpFunnelSide (i : Fin 3) : Set ℍ := sharpFunnelClosedDomain∩(sharpFunnelSideLine i).carrier

theorem sharpFunnelInnerSide_mem (z : ℍ) : z∈sharpFunnelSide 0 ↔
    Complex.normSq (z:ℂ)=13/36 ∧ z.re≤5/12 := by
  change (z∈sharpFunnelClosedDomain ∧ z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0
    (Real.sqrt 13/6) _).carrier) ↔ _
  rw [circle_carrier_iff_normSq]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs]
  constructor
  · rintro ⟨hz,he⟩
    refine ⟨he,?_⟩
    have ht:=hz.2.2
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at ht he
    nlinarith only [ht,he]
  · rintro ⟨he,hx⟩
    refine ⟨⟨he.ge,?_,?_⟩,he⟩
    · linarith only [he]
    · norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at he ⊢
      nlinarith only [he,hx]

theorem sharpFunnelOuterSide_mem (z : ℍ) : z∈sharpFunnelSide 1 ↔
    Complex.normSq (z:ℂ)=52/9 ∧ z.re≤5/3 := by
  change (z∈sharpFunnelClosedDomain ∧ z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0
    (2*Real.sqrt 13/3) _).carrier) ↔ _
  rw [circle_carrier_iff_normSq]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,mul_pow,hs]
  constructor
  · rintro ⟨hz,he⟩
    refine ⟨he,?_⟩
    have ht:=hz.2.2
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at ht he
    nlinarith only [ht,he]
  · rintro ⟨he,hx⟩
    refine ⟨⟨?_,he.le,?_⟩,he⟩
    · linarith only [he]
    · norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at he ⊢
      nlinarith only [he,hx]

theorem sharpFunnelTopSide_mem (z : ℍ) : z∈sharpFunnelSide 2 ↔
    Complex.normSq ((z:ℂ)-(13/6:ℂ))=13/4 ∧
      13/36≤Complex.normSq (z:ℂ) ∧ Complex.normSq (z:ℂ)≤52/9 := by
  change (z∈sharpFunnelClosedDomain ∧ z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (13/6)
    (Real.sqrt 13/2) _).carrier) ↔ _
  rw [circle_carrier_iff_normSq]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  norm_num [div_pow,hs]
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨he,hz.1,hz.2.1⟩
  · rintro ⟨he,hlo,hhi⟩
    exact ⟨⟨hlo,hhi,he.ge⟩,he⟩

theorem sharpFunnelDomain_frontier_eq_sides : frontier sharpFunnelDomain=⋃i : Fin 3,sharpFunnelSide i := by
  ext z
  constructor
  · intro hz
    have hc : z∈sharpFunnelClosedDomain := sharpFunnelDomain_closure ▸ frontier_subset_closure hz
    rcases sharpFunnelDomain_frontier_subset hz with (h0|h1)|h2
    · exact mem_iUnion.mpr ⟨0,hc,h0⟩
    · exact mem_iUnion.mpr ⟨1,hc,h1⟩
    · exact mem_iUnion.mpr ⟨2,hc,h2⟩
  · intro hz
    obtain ⟨i,hi⟩:=mem_iUnion.mp hz
    rw [sharpFunnelDomain_open.frontier_eq,sharpFunnelDomain_closure]
    refine ⟨hi.1,?_⟩
    intro hD
    fin_cases i
    · have he:=((sharpFunnelInnerSide_mem z).mp hi).1
      exact hD.1.ne' he
    · have he:=((sharpFunnelOuterSide_mem z).mp hi).1
      exact hD.2.1.ne he
    · have he:=((sharpFunnelTopSide_mem z).mp hi).1
      exact hD.2.2.ne' he

theorem sharpFunnel_dilation_side_iff (z : ℍ) : sharpCollarD • z∈sharpFunnelSide 1 ↔ z∈sharpFunnelSide 0 := by
  rw [sharpFunnelOuterSide_mem,sharpFunnelInnerSide_mem,sharpCollarD_coe,Complex.normSq_mul]
  have hre : (sharpCollarD • z:ℍ).re=4*z.re:=by
    have h:=congrArg Complex.re (sharpCollarD_coe z)
    norm_num [Complex.mul_re,UpperHalfPlane.coe_re] at h
    exact h
  rw [hre]
  norm_num
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith only [h1,h2]

/-- The original hyperbolic generator pairs the two genuine radial sides. -/
theorem sharpFunnel_dilation_side_pair : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) '' sharpFunnelSide 0=sharpFunnelSide 1 := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact (sharpFunnel_dilation_side_iff z).mpr hz
  · intro z hz
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹
      z,?_,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD).apply_inv_self z⟩
    apply (sharpFunnel_dilation_side_iff _).mp
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarD) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹ z)∈sharpFunnelSide 1
    simpa only [IsometryEquiv.apply_inv_self] using hz

theorem sharpFunnelMiddleMirror_closedDomain (z : ℍ) (hz : z∈sharpFunnelClosedDomain) :
    sharpFunnelMiddleMirror z∈sharpFunnelClosedDomain := by
  have hv : 0<Complex.normSq (z:ℂ):=Complex.normSq_pos.mpr z.ne_zero
  have hnorm:=sharpFunnelMiddleMirror_norm_product z
  have he : Complex.normSq (sharpFunnelMiddleMirror z:ℂ)=(169/81)/Complex.normSq (z:ℂ) :=
    (eq_div_iff hv.ne').mpr hnorm
  refine ⟨?_,?_,?_⟩
  · rw [he]
    apply (le_div_iff₀ hv).mpr
    nlinarith only [hz.2.1]
  · rw [he]
    apply (div_le_iff₀ hv).mpr
    nlinarith only [hz.1]
  · have h:=sharpFunnelMiddleMirror_top_sign z
    have hp : 0≤(Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ))-13/4)*Complex.normSq (z:ℂ):=by
      nlinarith only [h,hz.2.2]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hv).mp hp)

theorem sharpFunnelMiddleMirror_topSide (z : ℍ) (hz : z∈sharpFunnelSide 2) :
    sharpFunnelMiddleMirror z∈sharpFunnelSide 2 := by
  have he:=((sharpFunnelTopSide_mem z).mp hz).1
  have hp:=sharpFunnelMiddleMirror_top_sign z
  have hv : 0<Complex.normSq (z:ℂ):=Complex.normSq_pos.mpr z.ne_zero
  have hzero : Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ))=13/4 := by
    rw [he,sub_self,mul_zero] at hp
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hv.ne')
  have hc:=sharpFunnelMiddleMirror_closedDomain z hz.1
  exact (sharpFunnelTopSide_mem _).mpr ⟨hzero,hc.1,hc.2.1⟩

theorem sharpFunnel_halfturn_topSide (z : ℍ) (hz : z∈sharpFunnelSide 2) :
    sharpCollarF • z∈sharpFunnelSide 2 := by
  have hb:=sharpFunnelMiddleMirror_topSide z hz
  have hfix : sharpFunnelTopMirror (sharpFunnelMiddleMirror z)=sharpFunnelMiddleMirror z :=
    (sharpFunnelTopLine.reflection_fixed_iff _).mpr hb.2
  have he:=congrArg (fun f : ℍ≃ᵢℍ=>f z) sharpFunnel_top_middle_product
  change sharpFunnelTopMirror (sharpFunnelMiddleMirror z)=sharpCollarF • z at he
  rw [←he,hfix]
  exact hb

/-- The actual order-two generator pairs the finite top side with itself. -/
theorem sharpFunnel_halfturn_side_pair : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF) '' sharpFunnelSide 2=sharpFunnelSide 2 := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact sharpFunnel_halfturn_topSide z hz
  · intro z hz
    refine ⟨sharpCollarF • z,sharpFunnel_halfturn_topSide z hz,?_⟩
    have h2 : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)=1 := by
      simpa only [←pow_two,sharpFunnelF_native_order] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF)
    exact congrArg (fun f : ℍ≃ᵢℍ=>f z) h2

theorem sharpFunnelOuterSide_closed_tile : sharpFunnelSide 1=
    sharpFunnelClosedDomain∩((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) '' sharpFunnelClosedDomain) := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1,?_⟩
    obtain ⟨y,hy,he⟩:=sharpFunnel_dilation_side_pair.symm ▸ hz
    exact ⟨y,hy.1,he⟩
  · rintro ⟨hz,y,hy,rfl⟩
    apply (sharpFunnelOuterSide_mem _).mpr
    have hn : Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) y:ℂ)=16*Complex.normSq (y:ℂ):=by
      change Complex.normSq ((sharpCollarD • y:ℍ):ℂ)=_
      rw [sharpCollarD_coe,Complex.normSq_mul]
      norm_num
    have he : Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) y:ℂ)=52/9:=by
      nlinarith only [hn,hy.1,hz.2.1]
    have hcl : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) y∈sharpFunnelSide 1:=by
      refine ⟨hz,?_⟩
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        sharpCollarD) y∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (2*Real.sqrt 13/3)
        _).carrier
      rw [circle_carrier_iff_normSq]
      have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
      norm_num [div_pow,mul_pow,hs]
      exact he
    exact (sharpFunnelOuterSide_mem _).mp hcl

theorem sharpFunnelInnerSide_closed_tile : sharpFunnelSide 0=
    sharpFunnelClosedDomain∩(((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹ : ℍ≃ᵢℍ) '' sharpFunnelClosedDomain) := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) z,
      ((sharpFunnel_dilation_side_iff z).mpr hz).1,?_⟩
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD).inv_apply_self z
  · rintro ⟨hz,y,hy,rfl⟩
    have hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹ y)∈sharpFunnelSide 1:=by
      rw [sharpFunnelOuterSide_closed_tile]
      exact ⟨by simpa only [IsometryEquiv.apply_inv_self] using hy,
        _,hz,rfl⟩
    exact (sharpFunnel_dilation_side_iff _).mp hd

theorem sharpFunnel_halfturn_top_nonpos (z : ℍ) (hz : z∈sharpFunnelClosedDomain) :
    Complex.normSq ((sharpCollarF • z:ℍ):ℂ)-(2*(13/6)*(sharpCollarF • z:ℍ).re)+(13/6)^2-13/4≤0 := by
  have hb:=sharpFunnelMiddleMirror_closedDomain z hz
  have hp:=sharpFunnelTopMirror_top_sign (sharpFunnelMiddleMirror z)
  have hd : 0<Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ)):=
    Complex.normSq_pos.mpr (by
      intro h
      have hi:=congrArg Complex.im h
      simp only [Complex.sub_im,UpperHalfPlane.coe_im] at hi
      norm_num at hi
      exact (sharpFunnelMiddleMirror z).im_pos.ne' hi)
  have hnon : (Complex.normSq ((sharpFunnelTopMirror (sharpFunnelMiddleMirror z):ℂ)-(13/6:ℂ))-13/4)*
      Complex.normSq ((sharpFunnelMiddleMirror z:ℂ)-(13/6:ℂ))≤0 :=by
    nlinarith only [hp,hb.2.2]
  have he:=congrArg (fun f : ℍ≃ᵢℍ=>f z) sharpFunnel_top_middle_product
  change sharpFunnelTopMirror (sharpFunnelMiddleMirror z)=sharpCollarF • z at he
  rw [he] at hnon
  have hn:=nonpos_of_mul_nonpos_left hnon hd
  norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn ⊢
  nlinarith only [hn]

theorem sharpFunnelTopSide_closed_tile : sharpFunnelSide 2=
    sharpFunnelClosedDomain∩((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF) '' sharpFunnelClosedDomain) := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1,?_⟩
    obtain ⟨y,hy,he⟩:=sharpFunnel_halfturn_side_pair.symm ▸ hz
    exact ⟨y,hy.1,he⟩
  · rintro ⟨hz,y,hy,rfl⟩
    apply (sharpFunnelTopSide_mem _).mpr
    refine ⟨?_,hz.1,hz.2.1⟩
    have hn:=sharpFunnel_halfturn_top_nonpos y hy
    have hp:=hz.2.2
    norm_num [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn hp ⊢
    nlinarith only [hn,hp]

theorem sharpFunnelVertex_mem_inner_top : sharpFunnelVertex∈sharpFunnelSide 0 ∧ sharpFunnelVertex∈sharpFunnelSide 2 := by
  constructor
  · apply (sharpFunnelInnerSide_mem _).mpr
    exact ⟨sharpFunnelVertex_normSq,by norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]⟩
  · apply (sharpFunnelTopSide_mem _).mpr
    refine ⟨sharpFunnelVertex_top_circle,sharpFunnelVertex_normSq.ge,?_⟩
    rw [sharpFunnelVertex_normSq]
    norm_num

theorem sharpFunnel_side_nontrivial (i : Fin 3) : (sharpFunnelSide i).Nontrivial := by
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hr : 0<Real.sqrt 13/6:=div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.sqrt 13/6) hr∈sharpFunnelSide 0:=by
    apply (sharpFunnelInnerSide_mem _).mpr
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
    nlinarith only [hs]
  have hne : sharpFunnelVertex≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.sqrt 13/6) hr:=by
    intro he
    have hx:=congrArg UpperHalfPlane.re he
    norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hx
  have h0 : (sharpFunnelSide 0).Nontrivial:=⟨_,sharpFunnelVertex_mem_inner_top.1,_,hv,hne⟩
  fin_cases i
  · exact h0
  · change (sharpFunnelSide 1).Nontrivial
    rw [←sharpFunnel_dilation_side_pair]
    exact h0.image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD).injective
  · refine ⟨_,sharpFunnelVertex_mem_inner_top.2,_,sharpFunnel_halfturn_topSide _ sharpFunnelVertex_mem_inner_top.2,?_⟩
    rw [sharpFunnelVertex_halfturn]
    intro he
    have hx:=congrArg UpperHalfPlane.re he
    rw [show (sharpCollarD • sharpFunnelVertex:ℍ).re=4*sharpFunnelVertex.re from by
      have h:=congrArg Complex.re (sharpCollarD_coe sharpFunnelVertex)
      norm_num [Complex.mul_re,UpperHalfPlane.coe_re] at h
      exact h] at hx
    norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hx

/-- The actual native neighbors of the three geometric sides. -/
def sharpFunnelSideNeighbor : Fin 3→sharpFunnelNativeGroup := ![
  ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)⁻¹,sharpFunnelNativeGroup.inv_mem
    sharpFunnelNative_generators_mem.2⟩,
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD,sharpFunnelNative_generators_mem.2⟩,
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF,sharpFunnelNative_generators_mem.1⟩]

theorem sharpFunnelSideNeighbor_ne_one (i : Fin 3) : sharpFunnelSideNeighbor i≠1 := by
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD≠1:=by
    intro h
    have he:=congrArg (fun g : ℍ≃ᵢℍ=>(g sharpFunnelCenter).im) h
    change (sharpCollarD • sharpFunnelCenter:ℍ).im=sharpFunnelCenter.im at he
    have hc:=congrArg Complex.im (sharpCollarD_coe sharpFunnelCenter)
    norm_num [Complex.mul_im,UpperHalfPlane.coe_im] at hc
    linarith only [he,hc,sharpFunnelCenter.im_pos]
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarF≠1:=by
    intro h
    have ho:=sharpFunnelF_native_order
    rw [h,orderOf_one] at ho
    norm_num at ho
  apply Subtype.coe_ne_coe.mp
  fin_cases i
  · exact inv_ne_one.mpr hD
  · exact hD
  · exact hF

theorem sharpFunnelSide_closed_tile (i : Fin 3) : sharpFunnelSide i=
    closure sharpFunnelDomain∩((sharpFunnelSideNeighbor i).val '' closure sharpFunnelDomain) := by
  rw [sharpFunnelDomain_closure]
  fin_cases i
  · exact sharpFunnelInnerSide_closed_tile
  · exact sharpFunnelOuterSide_closed_tile
  · exact sharpFunnelTopSide_closed_tile

def sharpFunnelOriginalSide (i : Fin 3) : Set sharpFunnelDiscData.domain.carrier :=
  sharpFunnelDiscCoordinate '' sharpFunnelSide i

theorem sharpFunnelDiscCoordinate_tile (g : sharpFunnelNativeGroup) :
    sharpFunnelDiscCoordinate '' (g.val '' closure sharpFunnelDomain)=
      fuchsianDomainTile sharpFunnelDiscData (sharpFunnelDiscCoordinate '' sharpFunnelDomain)
        (sharpFunnelDiscGroupEquiv g) := by
  change sharpFunnelDiscCoordinate '' (g.val '' closure sharpFunnelDomain)=
    (fun x=>sharpFunnelDiscGroupEquiv g • x) '' closure (sharpFunnelDiscCoordinate '' sharpFunnelDomain)
  rw [←sharpFunnelDiscCoordinate.image_closure]
  simp only [image_image]
  congr 1
  exact funext (sharpFunnelDiscCoordinate_equivariant g)

theorem sharpFunnelOriginalSide_closed_tile (i : Fin 3) : sharpFunnelOriginalSide i=
    closure (sharpFunnelDiscCoordinate '' sharpFunnelDomain)∩
      fuchsianDomainTile sharpFunnelDiscData (sharpFunnelDiscCoordinate '' sharpFunnelDomain)
        (sharpFunnelDiscGroupEquiv (sharpFunnelSideNeighbor i)) := by
  rw [sharpFunnelOriginalSide,sharpFunnelSide_closed_tile,image_inter sharpFunnelDiscCoordinate.injective,
    sharpFunnelDiscCoordinate.image_closure,sharpFunnelDiscCoordinate_tile]

/-- Each displayed geometric boundary piece is a genuine side of the original whole-group polygon. -/
theorem sharpFunnelOriginalSide_isSide (i : Fin 3) : IsFuchsianPolygonSide sharpFunnelDiscData
    (sharpFunnelDiscCoordinate '' sharpFunnelDomain) (sharpFunnelOriginalSide i) := by
  rw [sharpFunnelOriginalSide_closed_tile]
  apply sharpFunnelDomain_original_polygon.side_of_nontrivial_intersection
  · intro he
    apply sharpFunnelSideNeighbor_ne_one i
    exact sharpFunnelDiscGroupEquiv.injective (he.trans (map_one sharpFunnelDiscGroupEquiv).symm)
  · rw [←sharpFunnelOriginalSide_closed_tile]
    exact (sharpFunnel_side_nontrivial i).image sharpFunnelDiscCoordinate.injective


theorem sharpFunnelOriginal_frontier : frontier (sharpFunnelDiscCoordinate '' sharpFunnelDomain)=
    ⋃i : Fin 3,sharpFunnelOriginalSide i := by
  rw [←sharpFunnelDiscCoordinate.image_frontier,sharpFunnelDomain_frontier_eq_sides,image_iUnion]
  rfl

theorem sharpFunnelOriginalSide_support (i : Fin 3) :
    sharpFunnelDiscData.finiteCoordinate '' sharpFunnelOriginalSide i⊆(sharpFunnelSideLine i).toDiscLine.carrier := by
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  rw [show sharpFunnelDiscData.finiteCoordinate (sharpFunnelDiscCoordinate
    z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z from
    sharpCollarHalfPlaneData.cayleyCoordinate_finite z]
  exact ((sharpFunnelSideLine i).mem_discCarrier _).mpr (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hz.2)

/-- No additional unlisted sides occur in the original three-wall polygon. -/
theorem sharpFunnelOriginalSide_exhaustive {S : Set sharpFunnelDiscData.domain.carrier}
    (hS : IsFuchsianPolygonSide sharpFunnelDiscData (sharpFunnelDiscCoordinate '' sharpFunnelDomain) S) :
    ∃i : Fin 3,S=sharpFunnelOriginalSide i := by
  let f:=sharpFunnelDiscData.finiteCoordinate
  obtain ⟨L,hL⟩:=hS.2.1.2
  have hcon : IsPreconnected (f '' S):=hS.2.1.1.isPreconnected
  have hnt : (f '' S).Nontrivial:=hS.2.2.image f.injective
  have sharpFunnelDiscT1 : T1Space Complex.UnitDisc:=Complex.UnitDisc.isEmbedding_coe.t1Space
  have hinf : (f '' S).Infinite:=IsPreconnected.infinite_of_nontrivial hcon hnt
  have hsub : f '' S⊆⋃i : Fin 3,(sharpFunnelSideLine i).toDiscLine.carrier:=by
    rintro _ ⟨x,hx,rfl⟩
    have hxB:=hS.subset_frontier sharpFunnelDomain_original_polygon.locallyFinite.fundamental hx
    rw [sharpFunnelOriginal_frontier] at hxB
    obtain ⟨i,hi⟩:=mem_iUnion.mp hxB
    exact mem_iUnion.mpr ⟨i,sharpFunnelOriginalSide_support i ⟨x,hi,rfl⟩⟩
  have hex : ∃i : Fin 3,L=(sharpFunnelSideLine i).toDiscLine:=by
    by_contra hn
    have hne : ∀i : Fin 3,L≠(sharpFunnelSideLine i).toDiscLine:=by simpa only [not_exists] using hn
    have hfin : (⋃i : Fin 3,L.carrier∩(sharpFunnelSideLine i).toDiscLine.carrier).Finite:=
      Set.finite_iUnion (fun i=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.inter_subsingleton (hne
        i)).finite)
    apply hinf (hfin.subset ?_)
    intro x hx
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hsub hx)
    exact mem_iUnion.mpr ⟨i,hL hx,hi⟩
  obtain ⟨i,hi⟩:=hex
  have hSS : S⊆sharpFunnelOriginalSide i:=by
    intro x hx
    obtain ⟨z,rfl⟩:=sharpFunnelDiscCoordinate.surjective x
    refine ⟨z,⟨?_,?_⟩,rfl⟩
    · have hxcl:=frontier_subset_closure (hS.subset_frontier
      sharpFunnelDomain_original_polygon.locallyFinite.fundamental hx)
      rw [←sharpFunnelDiscCoordinate.image_closure] at hxcl
      obtain ⟨u,hu,he⟩:=hxcl
      have heq:=sharpFunnelDiscCoordinate.injective he
      exact sharpFunnelDomain_closure ▸ heq ▸ hu
    · have hl:=hL ⟨sharpFunnelDiscCoordinate z,hx,rfl⟩
      rw [hi] at hl
      change sharpFunnelDiscData.finiteCoordinate (sharpFunnelDiscCoordinate z)∈(sharpFunnelSideLine
        i).toDiscLine.carrier at hl
      rw [show sharpFunnelDiscData.finiteCoordinate (sharpFunnelDiscCoordinate
        z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z from
        sharpCollarHalfPlaneData.cayleyCoordinate_finite z] at hl
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using ((sharpFunnelSideLine i).mem_discCarrier _).mp hl
  have hntS:=hS.2.2
  obtain ⟨⟨g,hg,hge⟩,_⟩:=hS
  have hni : sharpFunnelDiscGroupEquiv (sharpFunnelSideNeighbor i)≠1:=by
    intro he
    exact sharpFunnelSideNeighbor_ne_one i (sharpFunnelDiscGroupEquiv.injective (he.trans (map_one _).symm))
  have hgi : g=sharpFunnelDiscGroupEquiv (sharpFunnelSideNeighbor i):=by
    by_contra hne
    have hs:=sharpFunnelDomain_original_polygon.closed_tile_triple_subsingleton hg hni hne
    obtain ⟨x,hx,y,hy,hxy⟩:=hntS
    have hxi:=hSS hx
    have hyi:=hSS hy
    rw [sharpFunnelOriginalSide_closed_tile] at hxi hyi
    exact hxy (hs ⟨hge ▸ hx,hxi.2⟩ ⟨hge ▸ hy,hyi.2⟩)
  exact ⟨i,hge.trans (hgi ▸ (sharpFunnelOriginalSide_closed_tile i).symm)⟩

theorem sharpFunnelOriginalSide_injective : Function.Injective sharpFunnelOriginalSide := by
  have hp0:=sharpFunnelVertex_mem_inner_top.1
  have hp2:=sharpFunnelVertex_mem_inner_top.2
  have hq2:=sharpFunnel_halfturn_topSide _ hp2
  rw [sharpFunnelVertex_halfturn] at hq2
  have hq1:=(sharpFunnel_dilation_side_iff sharpFunnelVertex).mpr hp0
  have hp1 : sharpFunnelVertex∉sharpFunnelSide 1:=by
    intro h
    have hn:=((sharpFunnelOuterSide_mem _).mp h).1
    rw [sharpFunnelVertex_normSq] at hn
    norm_num at hn
  have hq0 : sharpCollarD • sharpFunnelVertex∉sharpFunnelSide 0:=by
    intro h
    have hn:=((sharpFunnelInnerSide_mem _).mp h).1
    rw [sharpFunnelVertex_dilation_normSq] at hn
    norm_num at hn
  intro i j he
  have hs : sharpFunnelSide i=sharpFunnelSide j:=image_injective.mpr sharpFunnelDiscCoordinate.injective he
  fin_cases i <;> fin_cases j <;> try rfl
  · exact False.elim (hp1 (hs ▸ hp0))
  · exact False.elim (hq0 (hs.symm ▸ hq2))
  · exact False.elim (hp1 (hs.symm ▸ hp0))
  · exact False.elim (hp1 (hs.symm ▸ hp2))
  · exact False.elim (hq0 (hs ▸ hq2))
  · exact False.elim (hp1 (hs ▸ hp2))

/-- The polygon has exactly three sides in the literal original side type. -/
def sharpFunnelSidesEquiv : Fin 3≃FuchsianPolygonSides sharpFunnelDiscData
    (sharpFunnelDiscCoordinate '' sharpFunnelDomain) :=
  Equiv.ofBijective (fun i=>⟨sharpFunnelOriginalSide i,sharpFunnelOriginalSide_isSide i⟩)
    ⟨fun _ _ he=>sharpFunnelOriginalSide_injective (congrArg Subtype.val he),by
      intro S
      obtain ⟨i,hi⟩:=sharpFunnelOriginalSide_exhaustive S.property
      exact ⟨i,Subtype.ext hi.symm⟩⟩

theorem sharpFunnelOriginalSide_card : Nat.card (FuchsianPolygonSides sharpFunnelDiscData
    (sharpFunnelDiscCoordinate '' sharpFunnelDomain))=3 := by
  rw [←Nat.card_congr sharpFunnelSidesEquiv]
  simp

theorem sharpFunnelDiscCoordinate_action_image (g : sharpFunnelNativeGroup) (S : Set ℍ) :
    (sharpFunnelDiscGroupEquiv g) • (sharpFunnelDiscCoordinate '' S)=sharpFunnelDiscCoordinate '' (g.val '' S) := by
  change (fun x=>sharpFunnelDiscGroupEquiv g • x) '' (sharpFunnelDiscCoordinate '' S)=_
  simp only [image_image]
  congr 1
  exact (funext (sharpFunnelDiscCoordinate_equivariant g)).symm

/-- The original hyperbolic generator genuinely pairs the two infinite sides. -/
theorem sharpFunnelOriginal_dilation_pair :
    sharpFunnelDiscGroupEquiv ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarD,sharpFunnelNative_generators_mem.2⟩ •
      sharpFunnelOriginalSide 0=sharpFunnelOriginalSide 1 := by
  rw [sharpFunnelOriginalSide,sharpFunnelDiscCoordinate_action_image,sharpFunnel_dilation_side_pair]
  rfl

/-- The original order-two generator genuinely pairs the finite side with itself. -/
theorem sharpFunnelOriginal_halfturn_pair :
    sharpFunnelDiscGroupEquiv ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      sharpCollarF,sharpFunnelNative_generators_mem.1⟩ •
      sharpFunnelOriginalSide 2=sharpFunnelOriginalSide 2 := by
  rw [sharpFunnelOriginalSide,sharpFunnelDiscCoordinate_action_image,sharpFunnel_halfturn_side_pair]


def sharpFunnelInnerProbe : ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.sqrt 13/6) (by positivity)

theorem sharpFunnelInnerProbe_mem_side : sharpFunnelInnerProbe∈sharpFunnelSide 0 := by
  apply (sharpFunnelInnerSide_mem _).mpr
  norm_num [sharpFunnelInnerProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤13)]

theorem sharpFunnelVertex_ne_innerProbe : sharpFunnelVertex≠sharpFunnelInnerProbe := by
  intro he
  have hx:=congrArg UpperHalfPlane.re he
  norm_num [sharpFunnelVertex,sharpFunnelInnerProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hx

theorem sharpFunnelVertex_ne_dilation : sharpFunnelVertex≠sharpCollarD • sharpFunnelVertex := by
  intro he
  have hx:=congrArg (fun z : ℍ=>(z:ℂ).re) he
  rw [sharpCollarD_coe] at hx
  norm_num [Complex.mul_re,sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hx

def sharpFunnelTopRay : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt sharpFunnelVertex:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough sharpFunnelVertex (sharpCollarD •
    sharpFunnelVertex) sharpFunnelVertex_ne_dilation

def sharpFunnelInnerRay : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt sharpFunnelVertex:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough sharpFunnelVertex sharpFunnelInnerProbe sharpFunnelVertex_ne_innerProbe

theorem sharpFunnelInnerRay_support : sharpFunnelInnerRay.supportLine=sharpFunnelInnerLine := by
  apply sharpFunnelInnerRay.supportLine.eq_of_two_points sharpFunnelInnerLine sharpFunnelVertex_ne_innerProbe
    sharpFunnelInnerRay.start_mem_support
    (sharpFunnelInnerRay.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _))
    sharpFunnelVertex_mem_inner_top.1.2 sharpFunnelInnerProbe_mem_side.2

theorem sharpFunnelTopRay_support : sharpFunnelTopRay.supportLine=sharpFunnelTopLine := by
  apply sharpFunnelTopRay.supportLine.eq_of_two_points sharpFunnelTopLine sharpFunnelVertex_ne_dilation
    sharpFunnelTopRay.start_mem_support
    (sharpFunnelTopRay.subset_support (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _))
    sharpFunnelVertex_mem_inner_top.2.2
  have h:=sharpFunnel_halfturn_topSide _ sharpFunnelVertex_mem_inner_top.2
  rw [sharpFunnelVertex_halfturn] at h
  exact h.2

theorem sharpFunnel_corner_directions :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection sharpFunnelVertex (sharpCollarD •
      sharpFunnelVertex)=⟨5*Real.sqrt 3/8,35/8⟩ ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection sharpFunnelVertex sharpFunnelInnerProbe=⟨-5*Real.sqrt 3/24,25/72⟩ := by
  have hdRe : (sharpCollarD • sharpFunnelVertex:ℍ).re=5/3:=by
    have h:=congrArg Complex.re (sharpCollarD_coe sharpFunnelVertex)
    norm_num [Complex.mul_re,sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.coe_re] at h
    exact h
  have hdIm : (sharpCollarD • sharpFunnelVertex:ℍ).im=Real.sqrt 3:=by
    have h:=congrArg Complex.im (sharpCollarD_coe sharpFunnelVertex)
    norm_num [Complex.mul_im,sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.coe_im] at h
    change (sharpCollarD • sharpFunnelVertex:ℍ).im=4*(Real.sqrt 3/4) at h
    linarith only [h]
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have ht:=Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
  constructor
  · unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection
    rw [hdRe,hdIm]
    apply Complex.ext <;> norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    all_goals nlinarith only [hs]
  · apply Complex.ext <;> norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection,sharpFunnelVertex,sharpFunnelInnerProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    all_goals nlinarith only [hs,ht]

/-- The angle is measured from the actual forward directions along the two genuine sides. -/
theorem sharpFunnel_corner_angle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure sharpFunnelTopRay sharpFunnelInnerRay=Real.pi/3 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_eq_direction sharpFunnelTopRay
    sharpFunnelInnerRay
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) sharpFunnelVertex_ne_dilation.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) sharpFunnelVertex_ne_innerProbe.symm,
    sharpFunnel_corner_directions.1,sharpFunnel_corner_directions.2]
  have hs : (Real.sqrt 3)^2=3:=Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hv : ‖(⟨5*Real.sqrt 3/8,35/8⟩:ℂ)‖=5*Real.sqrt 13/4 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [←Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_apply]
    nlinarith only [hs,ht]
  have hw : ‖(⟨-5*Real.sqrt 3/24,25/72⟩:ℂ)‖=5*Real.sqrt 13/36 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [←Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_apply]
    nlinarith only [hs,ht]
  have hi : inner ℝ (⟨5*Real.sqrt 3/8,35/8⟩:ℂ) (⟨-5*Real.sqrt 3/24,25/72⟩:ℂ)=325/288 := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    norm_num
    nlinarith only [hs]
  have hc:=InnerProductGeometry.cos_angle_mul_norm_mul_norm
    (⟨5*Real.sqrt 3/8,35/8⟩:ℂ) (⟨-5*Real.sqrt 3/24,25/72⟩:ℂ)
  rw [hv,hw,hi] at hc
  apply Real.injOn_cos
    ⟨InnerProductGeometry.angle_nonneg _ _,InnerProductGeometry.angle_le_pi _ _⟩
    ⟨by positivity,by linarith only [Real.pi_pos]⟩
  rw [Real.cos_pi_div_three]
  nlinarith only [hc,ht]

theorem sharpFunnel_rays_proper : sharpFunnelTopRay.supportLine≠sharpFunnelInnerRay.supportLine := by
  rw [sharpFunnelTopRay_support,sharpFunnelInnerRay_support]
  intro he
  have hc : (13/6:ℝ)=0:=by injection he
  norm_num at hc

theorem circle_outside_iff_normSq (c r : ℝ) (hr : 0<r) (z : ℍ) :
    r<‖(z:ℂ)-(c:ℂ)‖ ↔ r^2<Complex.normSq ((z:ℂ)-(c:ℂ)) := by
  rw [Complex.normSq_eq_norm_sq]
  exact (sq_lt_sq₀ hr.le (norm_nonneg _)).symm

theorem sharpFunnelCorner_halfplanes :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior sharpFunnelTopRay sharpFunnelInnerRay=
      {z : ℍ | 13/36<Complex.normSq (z:ℂ) ∧ 13/4<Complex.normSq ((z:ℂ)-(13/6:ℂ))} := by
  have hTop : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleSide sharpFunnelTopRay sharpFunnelInnerRay=
      {z : ℍ | Real.sqrt 13/2<‖(z:ℂ)-(13/6:ℂ)‖} := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleSide_eq_component _ _ sharpFunnel_rays_proper
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _
        _,sharpFunnelVertex_ne_innerProbe.symm⟩,sharpFunnelTopRay_support]
    have hu : Real.sqrt 13/2<‖(sharpFunnelInnerProbe:ℂ)-((13/6:ℝ):ℂ)‖:=by
      rw [circle_outside_iff_normSq _ _ (by positivity)]
      have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
      norm_num [sharpFunnelInnerProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
      nlinarith only [hs]
    simpa only [sharpFunnelTopLine,Complex.ofReal_div,Complex.ofReal_ofNat] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_circle_outside (13/6) (Real.sqrt 13/2) (by positivity) sharpFunnelInnerProbe hu
  have hInner : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleSide sharpFunnelInnerRay sharpFunnelTopRay=
      {z : ℍ | Real.sqrt 13/6<‖(z:ℂ)-(0:ℂ)‖} := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleSide_eq_component _ _ sharpFunnel_rays_proper.symm
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _
        _,sharpFunnelVertex_ne_dilation.symm⟩,sharpFunnelInnerRay_support]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_circle_outside
    rw [circle_outside_iff_normSq _ _ (by positivity)]
    have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
    norm_num [sub_zero,sharpFunnelVertex_dilation_normSq,div_pow,hs]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior,hTop,hInner]
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq]
  have hs : (Real.sqrt 13)^2=13:=Real.sq_sqrt (by norm_num)
  have hT:=circle_outside_iff_normSq (13/6) (Real.sqrt 13/2) (by positivity) z
  have hI:=circle_outside_iff_normSq 0 (Real.sqrt 13/6) (by positivity) z
  norm_num [div_pow,hs] at hT hI
  rw [sub_zero,hT,hI]
  exact and_comm

/-- The measured angle is the genuine local interior of the specified funnel polygon. -/
theorem sharpFunnelCorner_interior_germ :
    ∃U : Set ℍ,IsOpen U ∧ sharpFunnelVertex∈U ∧
      U∩sharpFunnelDomain=U∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior sharpFunnelTopRay sharpFunnelInnerRay := by
  let U : Set ℍ:={z | Complex.normSq (z:ℂ)<52/9}
  refine ⟨U,isOpen_lt (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe) continuous_const,?_,?_⟩
  · change Complex.normSq (sharpFunnelVertex:ℂ)<52/9
    rw [sharpFunnelVertex_normSq]
    norm_num
  · rw [sharpFunnelCorner_halfplanes]
    ext z
    change (_∧_∧_∧_)↔(_∧_∧_)
    tauto

theorem sharpFunnelMiddleMirror_vertex : sharpFunnelMiddleMirror sharpFunnelVertex=sharpCollarD • sharpFunnelVertex := by
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 (Real.sqrt 13/3) _ sharpFunnelVertex:ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe,sharpCollarD_coe]
  norm_num only [Complex.ofReal_zero,zero_add]
  have hd : conj (sharpFunnelVertex:ℂ)-(0:ℂ)≠0:=by
    simpa only [sub_zero,map_ne_zero] using sharpFunnelVertex.ne_zero
  apply (div_eq_iff hd).mpr
  have hr : ((Real.sqrt 13/3:ℝ):ℂ)^2=(13/9:ℂ):=by
    have he : (Real.sqrt 13/3)^2=(13/9:ℝ):=by
      rw [div_pow,Real.sq_sqrt (by norm_num)]
      norm_num
    rw [←Complex.ofReal_pow,he]
    norm_num
  rw [hr]
  norm_num [sharpFunnelVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  all_goals nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
    Real.sq_sqrt (by norm_num : (0:ℝ)≤13)]

theorem sharpFunnelMiddleMirror_domain_image : sharpFunnelMiddleMirror '' sharpFunnelDomain=sharpFunnelDomain := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact sharpFunnelMiddleMirror_domain z hz
  · intro z hz
    refine ⟨sharpFunnelMiddleMirror z,sharpFunnelMiddleMirror_domain z hz,?_⟩
    exact congrArg (fun g : ℍ≃ᵢℍ=>g z) sharpFunnelMiddleMirror_sq

/-- Both finite corners of the specified region are genuine interior angles of size pi/3. -/
theorem sharpFunnel_both_corner_germs :
    ∀p∈({sharpFunnelVertex,sharpCollarD • sharpFunnelVertex} : Set ℍ),
      ∃R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/3 ∧
        ∃U : Set ℍ,IsOpen U ∧ p∈U ∧ U∩sharpFunnelDomain=U∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S := by
  intro p hp
  simp only [mem_insert_iff,mem_singleton_iff] at hp
  rcases hp with rfl|rfl
  · exact ⟨sharpFunnelTopRay,sharpFunnelInnerRay,sharpFunnel_corner_angle,sharpFunnelCorner_interior_germ⟩
  · let g:=sharpFunnelMiddleLine.reflectionMatrix
    have hg (z : ℍ) : g • z=sharpFunnelMiddleMirror z:=sharpFunnelMiddleLine.reflectionMatrix_action z
    have hp : g • sharpFunnelVertex=sharpCollarD • sharpFunnelVertex:=
      (hg _).trans sharpFunnelMiddleMirror_vertex
    rw [←hp]
    refine ⟨sharpFunnelTopRay.realGLMap g,sharpFunnelInnerRay.realGLMap g,?_,?_⟩
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_realGLMap,sharpFunnel_corner_angle]
    · obtain ⟨U,hU,hpU,he⟩:=sharpFunnelCorner_interior_germ
      refine ⟨(g • · : ℍ→ℍ) '' U,(Homeomorph.smul g : ℍ≃ₜℍ).isOpenMap U hU,⟨_,hpU,rfl⟩,?_⟩
      have hD : (g • · : ℍ→ℍ) '' sharpFunnelDomain=sharpFunnelDomain:=by
        simpa only [hg] using sharpFunnelMiddleMirror_domain_image
      rw [←hD,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_realGL_image _ _
        sharpFunnel_rays_proper g,
        ←image_inter (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry
          g).injective,he,image_inter (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective]


/-- Both named generators are the actual original Mobius transformations, not additional relabelled actions. -/
theorem sharpFunnelGroupEquiv_matrix (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈sharpFunnelNativeGroup) :
    (sharpFunnelGroupEquiv ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hA⟩).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := by
  rw [sharpFunnelGroupEquiv_val]
  exact nativeConformalSubgroupMobiusHom_matrix _ _ _ _

theorem sharpFunnelDiscGroupEquiv_matrix (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈sharpFunnelNativeGroup) :
    (sharpFunnelDiscGroupEquiv ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hA⟩).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*(sharpFunnelGroupEquiv
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    A,hA⟩).val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹=_
  rw [sharpFunnelGroupEquiv_matrix]

/-- The example's literal three-wall region is a genuine whole-group fundamental polygon;
its two finite corners have the actual stated interior angle. The earlier sharpness module
supplies discreteness, non-elementarity, axis simplicity, and equality in the collar bound. -/
theorem sharpFunnel_convex_three_side_polygon_with_two_vertices_angle_pi_div_three :
    IsConvexFuchsianPolygon sharpFunnelDiscData (sharpFunnelDiscCoordinate '' sharpFunnelDomain) ∧
    Nat.card (FuchsianPolygonSides sharpFunnelDiscData (sharpFunnelDiscCoordinate '' sharpFunnelDomain))=3 ∧
    (∀i : Fin 3,IsFuchsianPolygonSide sharpFunnelDiscData
      (sharpFunnelDiscCoordinate '' sharpFunnelDomain) (sharpFunnelOriginalSide i)) ∧
    (∀p∈({sharpFunnelVertex,sharpCollarD • sharpFunnelVertex} : Set ℍ),
      ∃R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/3 ∧
        ∃U : Set ℍ,IsOpen U ∧ p∈U ∧ U∩sharpFunnelDomain=U∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) :=
  ⟨sharpFunnelDomain_original_polygon,sharpFunnelOriginalSide_card,
    sharpFunnelOriginalSide_isSide,sharpFunnel_both_corner_germs⟩

end LowDimensionalTopology.Geometry.Fuchsian
