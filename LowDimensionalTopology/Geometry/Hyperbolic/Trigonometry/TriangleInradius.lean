module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleSideNormals
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section



def DiscLine.inradiusSign (L : DiscLine) (q : 𝔻) : ℝ :=
  let f := closedDiscKleinAffine L.incenterNormal L.incenterOffset (discToClosedModel q)
  f / |f|

def DiscLine.inradiusNormal (L : DiscLine) (q : 𝔻) : ℂ := L.inradiusSign q • L.incenterNormal

def DiscLine.inradiusOffset (L : DiscLine) (q : 𝔻) : ℝ := L.inradiusSign q * L.incenterOffset

theorem DiscLine.inradiusSign_sq (L : DiscLine) (q : 𝔻) (hq : q ∉ L.carrier) :
    L.inradiusSign q ^ 2 = 1 := by
  have hf : closedDiscKleinAffine L.incenterNormal L.incenterOffset (discToClosedModel q) ≠ 0 := by
    intro h
    exact hq ((L.closedCarrier_mem_interior_iff q).mp ((L.closed_incenter_affine_zero_iff _).mp h))
  dsimp [DiscLine.inradiusSign]
  rw [div_pow,sq_abs,div_self (pow_ne_zero 2 hf)]

theorem DiscLine.inradiusNormal_distance (L : DiscLine) (q : 𝔻) :
    inner ℝ (L.inradiusNormal q)
        (halfPlaneKleinHeight (discToHalfPlane q) • kleinCoordinate q) -
      L.inradiusOffset q * halfPlaneKleinHeight (discToHalfPlane q) = Real.sinh (L.pointDist q) := by
  rw [L.sinh_pointDist_closed_incenter_affine]
  unfold DiscLine.inradiusNormal DiscLine.inradiusOffset DiscLine.inradiusSign
  simp only [real_inner_smul_left,inner_smul_right,closedDiscKleinAffine,
    closedKleinCoordinate_disc_inclusion]
  have he := real_div_abs_mul_self (inner ℝ L.incenterNormal (kleinCoordinate q) - L.incenterOffset)
  nlinarith only [congrArg (fun x : ℝ => halfPlaneKleinHeight (discToHalfPlane q) * x) he]





theorem sideNormals_equal_distance_gram (x nA nB nC : ℂ) (h tA tB tC s : ℝ)
    (hx : h ^ 2 - ‖x‖ ^ 2 = 1) (hh : h + 1 ≠ 0)
    (hA : ‖nA‖ ^ 2 - tA ^ 2 = 1) (hB : ‖nB‖ ^ 2 - tB ^ 2 = 1)
    (hC : ‖nC‖ ^ 2 - tC ^ 2 = 1)
    (hsA : inner ℝ nA x - tA * h = s) (hsB : inner ℝ nB x - tB * h = s)
    (hsC : inner ℝ nC x - tC * h = s) :
    let ab := inner ℝ nA nB - tA * tB
    let bc := inner ℝ nB nC - tB * tC
    let ca := inner ℝ nC nA - tC * tA
    (1 + s ^ 2) ^ 3 + 2 * (ab + s ^ 2) * (bc + s ^ 2) * (ca + s ^ 2) -
      (1 + s ^ 2) * ((ab + s ^ 2) ^ 2 + (bc + s ^ 2) ^ 2 + (ca + s ^ 2) ^ 2) = 0 := by
  dsimp only
  have hAt : h * tA - inner ℝ nA x = -s := by linarith
  have hBt : h * tB - inner ℝ nB x = -s := by linarith
  have hCt : h * tC - inner ℝ nC x = -s := by linarith
  have he := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three (sideNormalBoost x h nA
    tA) (sideNormalBoost x h nB tB)
    (sideNormalBoost x h nC tC)
  simp only [sideNormalBoost_inner x h _ _ _ _ hx hh,hAt,hBt,hCt,neg_mul_neg,
    real_inner_self_eq_norm_sq] at he
  have hA' : ‖nA‖ ^ 2 - tA * tA = 1 := by nlinarith only [hA]
  have hB' : ‖nB‖ ^ 2 - tB * tB = 1 := by nlinarith only [hB]
  have hC' : ‖nC‖ ^ 2 - tC * tC = 1 := by nlinarith only [hC]
  rw [hA',hB',hC'] at he
  nlinarith only [he]

/-- The three-normal Gram equation gives the exact radius expression. -/
theorem inradius_formula_of_gram (R a b c : ℝ)
    (ha : -1 < a) (hb : -1 < b) (hc : -1 < c)
    (hg : (1 + Real.sinh R ^ 2) ^ 3 +
      2 * (Real.sinh R ^ 2 - a) * (Real.sinh R ^ 2 - b) * (Real.sinh R ^ 2 - c) -
      (1 + Real.sinh R ^ 2) * ((Real.sinh R ^ 2 - a) ^ 2 +
        (Real.sinh R ^ 2 - b) ^ 2 + (Real.sinh R ^ 2 - c) ^ 2) = 0) :
    Real.tanh R ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c - 1) /
      (2 * (1 + a) * (1 + b) * (1 + c)) := by
  have ha' : 0 < 1 + a := by linarith
  have hb' : 0 < 1 + b := by linarith
  have hc' : 0 < 1 + c := by linarith
  have hd : 2 * (1 + a) * (1 + b) * (1 + c) ≠ 0 := ne_of_gt (by positivity)
  rw [Real.tanh_eq_sinh_div_cosh,div_pow]
  apply (div_eq_div_iff (pow_ne_zero 2 (Real.cosh_pos R).ne') hd).mpr
  rw [Real.cosh_sq]
  nlinarith only [hg]


theorem DiscLine.inradiusNormal_lorentz_unit (L : DiscLine) (q : 𝔻) (hq : q ∉ L.carrier) :
    ‖L.inradiusNormal q‖ ^ 2 - L.inradiusOffset q ^ 2 = 1 := by
  unfold DiscLine.inradiusNormal DiscLine.inradiusOffset
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_pow,L.inradiusSign_sq q hq]
  simpa only [one_mul,DiscLine.incenterNormal,DiscLine.incenterOffset] using L.toHalfPlane.incenterNormal_lorentz_unit

theorem DiscLine.inradiusNormal_inner (L M : DiscLine) (q : 𝔻) :
    inner ℝ (L.inradiusNormal q) (M.inradiusNormal q) -
        L.inradiusOffset q * M.inradiusOffset q =
      L.inradiusSign q * M.inradiusSign q *
        (inner ℝ L.incenterNormal M.incenterNormal - L.incenterOffset * M.incenterOffset) := by
  simp only [DiscLine.inradiusNormal,DiscLine.inradiusOffset,real_inner_smul_left,inner_smul_right]
  ring

theorem ClosedDiscTriangle.interior_not_sideLines (T : ClosedDiscTriangle) (q : 𝔻)
    (hq : q ∈ T.interior) : q ∉ T.sideLineA.carrier ∧ q ∉ T.sideLineB.carrier ∧ q ∉ T.sideLineC.carrier := by
  have hp := T.incenter_interior_coordinates hq
  refine ⟨?_,?_,?_⟩
  · intro h
    have he := (T.sideLineA_iff_coordinate (discToClosedModel q)).mp
      ((T.sideLineA.closedCarrier_mem_interior_iff q).mpr h)
    change (T.discCoordinate q).1 + (T.discCoordinate q).2 = 1 at he
    linarith [hp.2.2]
  · intro h
    have he := (T.sideLineB_iff_coordinate (discToClosedModel q)).mp
      ((T.sideLineB.closedCarrier_mem_interior_iff q).mpr h)
    change (T.discCoordinate q).1 = 0 at he
    linarith [hp.1]
  · intro h
    have he := (T.sideLineC_iff_coordinate (discToClosedModel q)).mp
      ((T.sideLineC.closedCarrier_mem_interior_iff q).mpr h)
    change (T.discCoordinate q).2 = 0 at he
    linarith [hp.2.1]

/-- Inward normalized normals of actual adjacent sides encode the actual finite or ideal angle. -/
theorem ClosedDiscTriangle.inradius_side_normal_cosine_alpha (T : ClosedDiscTriangle) (q : 𝔻)
    (hq : q ∈ T.interior) :
    inner ℝ (T.sideLineB.inradiusNormal q) (T.sideLineC.inradiusNormal q) -
      T.sideLineB.inradiusOffset q * T.sideLineC.inradiusOffset q = -Real.cos T.alpha := by
  have hn := T.interior_not_sideLines q hq
  have hB : closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
      (discToClosedModel q) ≠ 0 := by
    intro he
    exact hn.2.1 ((T.sideLineB.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineB.closed_incenter_affine_zero_iff _).mp he))
  have hC : closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
      (discToClosedModel q) ≠ 0 := by
    intro he
    exact hn.2.2 ((T.sideLineC.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineC.closed_incenter_affine_zero_iff _).mp he))
  have he := T.cosine_alpha_side_normals q hq
  rw [DiscLine.inradiusNormal_inner]
  dsimp only [DiscLine.inradiusSign]
  field_simp
  nlinarith only [he]

/-- The real incenter and genuine native side normals satisfy the singular planar Gram equation. -/
theorem ClosedDiscTriangle.inradius_gram (T : ClosedDiscTriangle) :
    (1 + Real.sinh T.inradius ^ 2) ^ 3 +
      2 * (Real.sinh T.inradius ^ 2 - Real.cos T.alpha) *
        (Real.sinh T.inradius ^ 2 - Real.cos T.beta) *
        (Real.sinh T.inradius ^ 2 - Real.cos T.gamma) -
      (1 + Real.sinh T.inradius ^ 2) *
        ((Real.sinh T.inradius ^ 2 - Real.cos T.alpha) ^ 2 +
          (Real.sinh T.inradius ^ 2 - Real.cos T.beta) ^ 2 +
          (Real.sinh T.inradius ^ 2 - Real.cos T.gamma) ^ 2) = 0 := by
  let q := T.incenter
  let h := halfPlaneKleinHeight (discToHalfPlane q)
  let x := h • kleinCoordinate q
  have hx : h ^ 2 - ‖x‖ ^ 2 = 1 := by
    simpa only [halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane] using
      halfPlaneKleinHeight_lorentz_unit (discToHalfPlane q)
  have hh : h + 1 ≠ 0 := ne_of_gt (by
    have hp : 0 < h := halfPlaneKleinHeight_pos (discToHalfPlane q)
    linarith)
  have hn := T.interior_not_sideLines q T.incenter_mem_interior
  have hsA : inner ℝ (T.sideLineA.inradiusNormal q) x - T.sideLineA.inradiusOffset q * h =
      Real.sinh T.inradius := T.sideLineA.inradiusNormal_distance q
  have hsB : inner ℝ (T.sideLineB.inradiusNormal q) x - T.sideLineB.inradiusOffset q * h =
      Real.sinh T.inradius := by
    rw [show Real.sinh T.inradius = Real.sinh (T.sideLineB.pointDist q) from
      congrArg Real.sinh T.inradius_eq_sideDist.2.1]
    exact T.sideLineB.inradiusNormal_distance q
  have hsC : inner ℝ (T.sideLineC.inradiusNormal q) x - T.sideLineC.inradiusOffset q * h =
      Real.sinh T.inradius := by
    rw [show Real.sinh T.inradius = Real.sinh (T.sideLineC.pointDist q) from
      congrArg Real.sinh T.inradius_eq_sideDist.2.2]
    exact T.sideLineC.inradiusNormal_distance q
  have he := sideNormals_equal_distance_gram x
    (T.sideLineA.inradiusNormal q) (T.sideLineB.inradiusNormal q) (T.sideLineC.inradiusNormal q)
    h (T.sideLineA.inradiusOffset q) (T.sideLineB.inradiusOffset q) (T.sideLineC.inradiusOffset q)
    (Real.sinh T.inradius) hx hh
    (T.sideLineA.inradiusNormal_lorentz_unit q hn.1)
    (T.sideLineB.inradiusNormal_lorentz_unit q hn.2.1)
    (T.sideLineC.inradiusNormal_lorentz_unit q hn.2.2) hsA hsB hsC
  have hbc := T.inradius_side_normal_cosine_alpha q T.incenter_mem_interior
  have hca := T.cycle.inradius_side_normal_cosine_alpha q
    (by rw [T.incenter_cycle_interior]; exact T.incenter_mem_interior)
  have hab := T.cycle.cycle.inradius_side_normal_cosine_alpha q
    (by rw [T.cycle.incenter_cycle_interior,T.incenter_cycle_interior]; exact T.incenter_mem_interior)
  change inner ℝ (T.sideLineC.inradiusNormal q) (T.sideLineA.inradiusNormal q) -
    T.sideLineC.inradiusOffset q * T.sideLineA.inradiusOffset q = -Real.cos T.beta at hca
  change inner ℝ (T.sideLineA.inradiusNormal q) (T.sideLineB.inradiusNormal q) -
    T.sideLineA.inradiusOffset q * T.sideLineB.inradiusOffset q = -Real.cos T.gamma at hab
  dsimp only at he
  rw [hab,hbc,hca] at he
  nlinarith only [he]

/-- For the actual positive metric inradius, including ideal triangles. -/
theorem ClosedDiscTriangle.tanh_inradius_sq_cosine_formula (T : ClosedDiscTriangle) :
    Real.tanh T.inradius ^ 2 =
      (Real.cos T.alpha ^ 2 + Real.cos T.beta ^ 2 + Real.cos T.gamma ^ 2 +
        2 * Real.cos T.alpha * Real.cos T.beta * Real.cos T.gamma - 1) /
      (2 * (1 + Real.cos T.alpha) * (1 + Real.cos T.beta) * (1 + Real.cos T.gamma)) := by
  have lower (θ : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) : -1 < Real.cos θ := by
    have he := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1 (le_refl Real.pi) hθ.2
    rwa [Real.cos_pi] at he
  exact inradius_formula_of_gram T.inradius (Real.cos T.alpha) (Real.cos T.beta) (Real.cos T.gamma)
    (lower _ T.alpha_mem_Ico) (lower _ T.cycle.alpha_mem_Ico)
    (lower _ T.cycle.cycle.alpha_mem_Ico) T.inradius_gram

end
end LowDimensionalTopology.Geometry.Hyperbolic
