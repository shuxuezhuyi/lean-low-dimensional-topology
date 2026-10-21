module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleIncenter
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine native Klein support functional is an open continuous map. -/
theorem native_support_isOpenMap {m : ℂ} (hm : m≠0) :
    IsOpenMap (fun z : ℍ=>inner ℝ m (halfPlaneKleinCoordinate z)) := by
  let f : ℂ→L[ℝ]ℝ:=innerSL ℝ m
  have hs : Function.Surjective f := by
    intro r
    refine ⟨(r/‖m‖^2) • m,?_⟩
    change inner ℝ m ((r/‖m‖^2) • m)=r
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  exact (f.isOpenMap hs).comp isOpenEmbedding_halfPlaneKleinCoordinate.isOpenMap

/-- The true closure of a native strict supporting half-plane is its original weak cut. -/
theorem native_support_cut_closure {m : ℂ} (hm : m≠0) (t : ℝ) :
    closure {z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)<t}=
      {z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)≤t} := by
  have hc : Continuous (fun z : ℍ=>inner ℝ m (halfPlaneKleinCoordinate z)) :=
    continuous_const.inner isOpenEmbedding_halfPlaneKleinCoordinate.continuous
  have he:=(native_support_isOpenMap hm).preimage_closure_eq_closure_preimage hc (Iio t)
  rw [closure_Iio] at he
  exact he.symm

/-- The actual component on the strict negative side of a native h-line is its true affine cut. -/
theorem native_open_halfPlane_eq_lt (N : HalfPlaneLine) (m : ℂ) (t : ℝ)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u : ℍ) (hu : inner ℝ m (halfPlaneKleinCoordinate u)<t) :
    openHHalfPlane N u={z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)<t} := by
  have huN : u∉N.carrier:=fun h=>(hu.ne ((hLine u).mp h))
  have hDisc : ∀z : 𝔻,z∈N.toDiscLine.carrier ↔inner ℝ m (kleinCoordinate z)=t := by
    intro z
    rw [DiscLine.mem_carrier,HalfPlaneLine.toDiscLine_toHalfPlane,hLine,
      halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane]
  apply cayleyHomeomorph.injective.image_injective
  change halfPlaneToDisc '' openHHalfPlane N u=halfPlaneToDisc '' _
  rw [cayley_image_openHHalfPlane N u huN,connectedComponentIn_discLine_lt N.toDiscLine m t hDisc
    (halfPlaneToDisc u) hu]
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change inner ℝ m (kleinCoordinate z)<t at hz
    change inner ℝ m (halfPlaneKleinCoordinate (discToHalfPlane z))<t
    simpa only [halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane] using hz
  · rintro ⟨w,hw,rfl⟩
    exact hw

/-- The genuine closed native half-plane component is the corresponding actual weak affine cut. -/
theorem native_closed_halfPlane_eq_le (N : HalfPlaneLine) (m : ℂ) (t : ℝ) (hm : m≠0)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u : ℍ) (hu : inner ℝ m (halfPlaneKleinCoordinate u)<t) :
    closedHHalfPlane N u={z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)≤t} := by
  rw [closedHHalfPlane,native_open_halfPlane_eq_lt N m t hLine u hu,native_support_cut_closure hm t]

/-- The actual component on the strict positive side of a native h-line is its true affine cut. -/
theorem native_open_halfPlane_eq_gt (N : HalfPlaneLine) (m : ℂ) (t : ℝ)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u : ℍ) (hu : t< inner ℝ m (halfPlaneKleinCoordinate u)) :
    openHHalfPlane N u={z : ℍ|t< inner ℝ m (halfPlaneKleinCoordinate z)} := by
  have hLineN (z : ℍ) : z∈N.carrier ↔inner ℝ (-m) (halfPlaneKleinCoordinate z)= -t := by
    rw [inner_neg_left,neg_inj,hLine]
  have huN : inner ℝ (-m) (halfPlaneKleinCoordinate u)< -t := by rw [inner_neg_left];linarith
  rw [native_open_halfPlane_eq_lt N (-m) (-t) hLineN u huN]
  ext z
  simp only [mem_ofPred_eq,inner_neg_left,neg_lt_neg_iff]

/-- The actual positive closed native component is the original weak positive half-plane. -/
theorem native_closed_halfPlane_eq_ge (N : HalfPlaneLine) (m : ℂ) (t : ℝ) (hm : m≠0)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u : ℍ) (hu : t< inner ℝ m (halfPlaneKleinCoordinate u)) :
    closedHHalfPlane N u={z : ℍ|t≤ inner ℝ m (halfPlaneKleinCoordinate z)} := by
  have hLineN (z : ℍ) : z∈N.carrier ↔inner ℝ (-m) (halfPlaneKleinCoordinate z)= -t := by
    rw [inner_neg_left,neg_inj,hLine]
  have huN : inner ℝ (-m) (halfPlaneKleinCoordinate u)< -t := by rw [inner_neg_left];linarith
  rw [native_closed_halfPlane_eq_le N (-m) (-t) (neg_ne_zero.mpr hm) hLineN u huN]
  ext z
  simp only [mem_ofPred_eq,inner_neg_left,neg_le_neg_iff]

/-- The true native complement components give exactly the two actual closed supporting half-planes. -/
theorem native_closed_halfPlane_cases (N : HalfPlaneLine) (m : ℂ) (t : ℝ) (hm : m≠0)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u : ℍ) (hu : u∉N.carrier) :
    closedHHalfPlane N u={z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)≤t} ∨
    closedHHalfPlane N u={z : ℍ|t≤ inner ℝ m (halfPlaneKleinCoordinate z)} := by
  have hne : inner ℝ m (halfPlaneKleinCoordinate u)≠t:=fun h=>hu ((hLine u).mpr h)
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact Or.inl (native_closed_halfPlane_eq_le N m t hm hLine u hn)
  · exact Or.inr (native_closed_halfPlane_eq_ge N m t hm hLine u hp)

/-- A genuine native isometry carrying one actual h-line to another carries their actual
complement components, with no orientation or fractional-linear coordinate assumption. -/
theorem native_image_open_halfPlane (f : ℍ≃ᵢℍ) (N M : HalfPlaneLine)
    (hLines : f '' N.carrier=M.carrier) (u : ℍ) (hu : u∉N.carrier) :
    f '' openHHalfPlane N u=openHHalfPlane M (f u) := by
  have he:=f.toHomeomorph.image_connectedComponentIn (show u∈N.carrierᶜ from hu)
  have hCompl : f '' N.carrierᶜ=M.carrierᶜ := by
    rw [←hLines]
    exact f.toHomeomorph.toEquiv.image_compl _
  change f '' openHHalfPlane N u=connectedComponentIn (f '' N.carrierᶜ) (f u) at he
  rw [hCompl] at he
  exact he

/-- Actual native isometries carry the actual closures of h-line complement components. -/
theorem native_image_closed_halfPlane (f : ℍ≃ᵢℍ) (N M : HalfPlaneLine)
    (hLines : f '' N.carrier=M.carrier) (u : ℍ) (hu : u∉N.carrier) :
    f '' closedHHalfPlane N u=closedHHalfPlane M (f u) := by
  change f '' closure (openHHalfPlane N u)=closure (openHHalfPlane M (f u))
  calc
    f '' closure (openHHalfPlane N u)=closure (f '' openHHalfPlane N u):=f.toHomeomorph.image_closure _
    _=closure (openHHalfPlane M (f u)):=congrArg closure (native_image_open_halfPlane f N M hLines u hu)

/-- At an actual point of a supporting line, its true closed half-plane contains no ambient neighborhood. -/
theorem native_support_closed_cut_not_nhds {m : ℂ} (hm : m≠0) (t : ℝ) (x : ℍ)
    (hx : inner ℝ m (halfPlaneKleinCoordinate x)=t) :
    {z : ℍ|inner ℝ m (halfPlaneKleinCoordinate z)≤t}∉𝓝 x := by
  intro hn
  have hImage : Iic t∈𝓝 (inner ℝ m (halfPlaneKleinCoordinate x)) :=
    (native_support_isOpenMap hm).nhds_le x hn
  rw [hx] at hImage
  have ht : t∈interior (Iic t):=mem_interior_iff_mem_nhds.mpr hImage
  simp only [interior_Iic,mem_Iio,lt_self_iff_false] at ht

/-- If two actual closed half-plane components of the same original h-line cover an ambient
neighborhood of a point on that line, they are opposite and overlap exactly on the original line. -/
theorem native_closed_halfPlanes_opposite (N : HalfPlaneLine) (m : ℂ) (t : ℝ) (hm : m≠0)
    (hLine : ∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t)
    (u v x : ℍ) (hu : u∉N.carrier) (hv : v∉N.carrier) (hx : x∈N.carrier)
    (hCover : closedHHalfPlane N u∪closedHHalfPlane N v∈𝓝 x) :
    closedHHalfPlane N u∩closedHHalfPlane N v=N.carrier := by
  have hNotLe:=native_support_closed_cut_not_nhds hm t x ((hLine x).mp hx)
  have hNotGe : {z : ℍ|t≤ inner ℝ m (halfPlaneKleinCoordinate z)}∉𝓝 x := by
    have hn:=native_support_closed_cut_not_nhds (neg_ne_zero.mpr hm) (-t) x (by
      rw [inner_neg_left,(hLine x).mp hx])
    simpa only [inner_neg_left,neg_le_neg_iff] using hn
  rcases native_closed_halfPlane_cases N m t hm hLine u hu with huEq | huEq <;>
    rcases native_closed_halfPlane_cases N m t hm hLine v hv with hvEq | hvEq
  · exact (hNotLe (by simpa only [huEq,hvEq,union_self] using hCover)).elim
  · rw [huEq,hvEq]
    ext z
    change (inner ℝ m (halfPlaneKleinCoordinate z)≤t ∧t≤ inner ℝ m (halfPlaneKleinCoordinate z))↔z∈N.carrier
    rw [hLine]
    exact ⟨fun h=>le_antisymm h.1 h.2,fun h=>⟨h.le,h.ge⟩⟩
  · rw [huEq,hvEq]
    ext z
    change (t≤ inner ℝ m (halfPlaneKleinCoordinate z) ∧ inner ℝ m (halfPlaneKleinCoordinate z)≤t)↔z∈N.carrier
    rw [hLine]
    exact ⟨fun h=>le_antisymm h.2 h.1,fun h=>⟨h.ge,h.le⟩⟩
  · exact (hNotGe (by simpa only [huEq,hvEq,union_self] using hCover)).elim

end LowDimensionalTopology.Geometry.Hyperbolic
