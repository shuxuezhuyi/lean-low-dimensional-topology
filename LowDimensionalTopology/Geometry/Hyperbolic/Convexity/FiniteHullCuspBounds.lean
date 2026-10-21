/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedLocalConvexity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine bounded horizontal-coordinate strip in the native upper half-plane. -/
def hCuspStrip (M : ℝ) : Set ℍ:={z | |z.re|<M}

/-- The actual native strip is geodesically convex. -/
theorem hCuspStrip_hConvex (M : ℝ) : HConvex (hCuspStrip M) := by
  have hl:=(hReCutLt_hConvex M).isometry_preimage (realGL_isometry UpperHalfPlane.J)
  have hr:=hReCutLt_hConvex M
  have he : hCuspStrip M=hReCutLt M∩((UpperHalfPlane.J•· : ℍ→ℍ) ⁻¹' hReCutLt M):=by
    ext z
    change |z.re|<M↔z.re<M∧(UpperHalfPlane.J•z).re<M
    have hJ : (UpperHalfPlane.J•z).re = -z.re := by
      change ((UpperHalfPlane.J•z : ℍ) : ℂ).re = _
      rw [UpperHalfPlane.coe_J_smul]
      simp only [Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re]
    rw [hJ,abs_lt]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [he]
  intro z hz w hw u hu
  exact ⟨hr z hz.1 w hw.1 hu,hl z hz.2 w hw.2 hu⟩

/-- Closing a genuine native convex set in the actual compactified disc preserves true closed hyperbolic convexity. -/
theorem DiscHConvex.closedModelClosure {S : Set 𝔻} (hS : DiscHConvex S) :
    ClosedDiscHConvex (discClosedModelClosure S) := by
  apply (closedDiscHConvex_iff_klein_convex _).mpr
  rw [discClosedModelClosure,closedKlein_image_discClosedModelClosure]
  exact ((discHConvex_iff_klein_convex S).mp hS).closure

/-- The genuine compactified strip in the disc model. -/
def closedCuspStrip (M : ℝ) : Set 𝕔𝔻:=
  discClosedModelClosure (halfPlaneToDisc '' hCuspStrip M)

/-- The compactified strip is convex for the actual finite-and-ideal geodesic segments. -/
theorem closedCuspStrip_hConvex (M : ℝ) : ClosedDiscHConvex (closedCuspStrip M):=
  ((hConvex_iff_cayley_discHConvex _).mp (hCuspStrip_hConvex M)).closedModelClosure

/-- Its genuine closed-half-plane coordinate has precisely the corresponding actual native-strip closure. -/
theorem mem_closedCuspStrip_iff (M : ℝ) (p : 𝕔𝔻) :
    p∈closedCuspStrip M↔closedModelCayleyHomeomorph.symm p∈halfPlaneClosedModelClosure (hCuspStrip M) := by
  rw [closedCuspStrip,←closedModelCayley_image_closure]
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa only [closedModelCayleyHomeomorph.symm_apply_apply] using hq
  · intro hp
    exact ⟨closedModelCayleyHomeomorph.symm p,hp,closedModelCayleyHomeomorph.apply_symm_apply p⟩

/-- Any finite actual point in the compactified strip retains the true bounded real coordinate. -/
theorem closedCuspStrip_finite_re_bound (M : ℝ) (p : 𝕔𝔻) (hp : p∈closedCuspStrip M)
    (z : ℂ) (hz : (closedModelCayleyHomeomorph.symm p).val=(z:OnePoint ℂ)) : |z.re|≤M := by
  have hq:=(mem_closedCuspStrip_iff M p).mp hp
  have hcl : (z:OnePoint ℂ)∈closure (extendedHalfPlanePoint '' hCuspStrip M):=by
    change (z:OnePoint ℂ)∈closure ((fun w : ℍ=>((w:ℂ):OnePoint ℂ)) '' hCuspStrip M)
    rw [←halfPlaneClosedModelClosure_ambient]
    exact ⟨closedModelCayleyHomeomorph.symm p,hq,hz⟩
  have he : extendedHalfPlanePoint '' hCuspStrip M=
      ((↑) : ℂ→OnePoint ℂ) '' (((↑) : ℍ→ℂ) '' hCuspStrip M):=by
    rw [image_image]
    rfl
  rw [he] at hcl
  have hzcl : z∈closure (((↑) : ℍ→ℂ) '' hCuspStrip M):=by
    have hh : z∈((↑) : ℂ→OnePoint ℂ) ⁻¹' closure (((↑) : ℂ→OnePoint ℂ) '' (((↑) : ℍ→ℂ) '' hCuspStrip M)):=hcl
    rwa [onePoint_coe_preimage_closure_image] at hh
  apply closure_minimal _ (isClosed_le (Complex.continuous_re.abs) continuous_const) hzcl
  rintro _ ⟨w,hw,rfl⟩
  exact hw.le

/-- The compactified strip contains every actual closed-half-plane point with strictly bounded finite real coordinate, including the genuine infinite point. -/
theorem closedCuspStrip_contains_point (M : ℝ) (hM : 0<M) (p : ClosedHalfPlaneModel)
    (hp : ∀z : ℂ,p.val=(z:OnePoint ℂ)→|z.re|<M) :
    closedModelCayleyHomeomorph p∈closedCuspStrip M := by
  rw [mem_closedCuspStrip_iff,closedModelCayleyHomeomorph.symm_apply_apply]
  have hvertical (x : ℝ) (hx : |x|<M) :
      closure (extendedHalfPlanePoint '' (HalfPlaneLine.vertical x).carrier)⊆
        closure (extendedHalfPlanePoint '' hCuspStrip M):=by
    apply closure_mono (image_mono _)
    intro z hz
    change z.re=x at hz
    change |z.re|<M
    rwa [hz]
  have hcl : p.val∈closure (extendedHalfPlanePoint '' hCuspStrip M):=by
    rcases p with ⟨p,hpH⟩
    cases p with
    | infty=>
      apply hvertical 0 (by simpa only [abs_zero] using hM)
      have hh : (∞:OnePoint ℂ)∈(HalfPlaneLine.vertical 0).idealEndpoints:=by
        rw [vertical_idealEndpoints]
        exact mem_insert_of_mem _ (mem_singleton _)
      exact hh.1
    | coe z=>
      have hzM:=hp z rfl
      have hzim : 0≤z.im:=(coe_mem_closedHalfPlaneSet z).mp hpH
      by_cases hzpos : 0<z.im
      · exact subset_closure (mem_image_of_mem extendedHalfPlanePoint (show (⟨z,hzpos⟩:ℍ)∈hCuspStrip M from hzM))
      · have hzim0 : z.im=0:=le_antisymm (le_of_not_gt hzpos) hzim
        have he : z=(z.re:ℂ):=by apply Complex.ext <;> simp [hzim0]
        change (z:OnePoint ℂ)∈closure (extendedHalfPlanePoint '' hCuspStrip M)
        rw [he]
        apply hvertical z.re hzM
        have hh : (((z.re:ℂ):OnePoint ℂ))∈(HalfPlaneLine.vertical z.re).idealEndpoints:=by
          rw [vertical_idealEndpoints]
          exact mem_insert _ _
        exact hh.1
  have hm : p.val∈(Subtype.val : ClosedHalfPlaneModel→OnePoint ℂ) '' halfPlaneClosedModelClosure (hCuspStrip M):=by
    rw [halfPlaneClosedModelClosure_ambient]
    exact hcl
  exact Subtype.val_injective.mem_set_image.mp hm

/-- Finite real magnitude at a finite sphere point; infinity contributes zero only to this auxiliary finite bound. -/
def sphereFiniteRealMagnitude : OnePoint ℂ → ℝ
  | .infty => 0
  | .some z => |z.re|

/-- The auxiliary finite-point magnitude is nonnegative at every genuine sphere point. -/
theorem sphereFiniteRealMagnitude_nonneg (p : OnePoint ℂ) : 0≤sphereFiniteRealMagnitude p := by
  cases p with
  | infty => exact le_refl _
  | coe z => exact abs_nonneg _

/-- True isometries preserve genuine closed convexity under preimages on the actual compactified model. -/
theorem ClosedDiscHConvex.isometry_closed_preimage {S : Set 𝕔𝔻}
    (hS : ClosedDiscHConvex S) (e : ClosedDiscIsometry) : ClosedDiscHConvex (e.closedMap ⁻¹' S) := by
  intro a ha b hb p hp
  apply hS (e.closedMap a) ha (e.closedMap b) hb
  rw [←e.image_closedModelDiscHSegment]
  exact mem_image_of_mem e.closedMap hp

/-- The actual closed hyperbolic hull of any finite genuine point family has uniformly bounded finite real coordinate in every actual upper-half-plane isometry chart. The genuine infinite point is permitted among the vertices. -/
theorem finite_closed_hull_cusp_re_bounded {n : ℕ} (v : Fin n→𝕔𝔻) (e : ClosedDiscIsometry) :
    ∃M : ℝ,0<M∧∀p : 𝕔𝔻,
      closedKleinCoordinate p∈convexHull ℝ (range (fun i=>closedKleinCoordinate (v i)))→
      ∀z : ℂ,(closedModelCayleyHomeomorph.symm (e.closedMap p)).val=(z:OnePoint ℂ)→|z.re|≤M := by
  classical
  let q : Fin n→ClosedHalfPlaneModel:=fun i=>closedModelCayleyHomeomorph.symm (e.closedMap (v i))
  let F : Fin n→ℝ:=fun i=>sphereFiniteRealMagnitude (q i).val
  let M : ℝ:=1+∑i,F i
  have hsum : 0≤∑i,F i:=Finset.sum_nonneg (fun i _=>sphereFiniteRealMagnitude_nonneg _)
  have hM : 0<M:=by dsimp only [M];linarith
  have hvertex (i : Fin n) : e.closedMap (v i)∈closedCuspStrip M:=by
    have hh : closedModelCayleyHomeomorph (q i)∈closedCuspStrip M:=by
      apply closedCuspStrip_contains_point M hM (q i)
      intro z hz
      have hi : F i≤∑j,F j:=Finset.single_le_sum
        (fun j _=>sphereFiniteRealMagnitude_nonneg (q j).val) (Finset.mem_univ i)
      have he : F i=|z.re|:=congrArg sphereFiniteRealMagnitude hz
      rw [he] at hi
      dsimp only [M]
      linarith
    simpa only [q,closedModelCayleyHomeomorph.apply_symm_apply] using hh
  let S:=e.closedMap ⁻¹' closedCuspStrip M
  have hS : ClosedDiscHConvex S:=(closedCuspStrip_hConvex M).isometry_closed_preimage e
  have hK : Convex ℝ (closedKleinCoordinate '' S):=(closedDiscHConvex_iff_klein_convex S).mp hS
  have hsub : range (fun i=>closedKleinCoordinate (v i))⊆closedKleinCoordinate '' S:=by
    rintro _ ⟨i,rfl⟩
    exact ⟨v i,hvertex i,rfl⟩
  refine ⟨M,hM,?_⟩
  intro p hp z hz
  have hpS : p∈S:=closedKleinCoordinate_injective.mem_set_image.mp ((convexHull_min hsub hK) hp)
  exact closedCuspStrip_finite_re_bound M (e.closedMap p) hpS z hz

end LowDimensionalTopology.Geometry.Hyperbolic
