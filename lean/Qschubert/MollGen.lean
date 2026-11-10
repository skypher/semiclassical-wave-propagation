import Qschubert.FormOps
import Qschubert.BoundedEvol
import Qschubert.SpecComp
import Qschubert.Evolution
import Qschubert.VAdj

/-!
# The mollified generator `Δ_ε(t)` and the mollified flow `V_ε`

For a real spectral cutoff `r` with `r` and `(1 + s) r(s)` bounded (`Cutoff`), `J = r(-Δ)` maps
`L²(ℍ)` into the domain of `-Δ` (`J_mem`), with `-Δ J = (s r)(-Δ)` (`negLapH_J`), and lifts to the
form space `Q` (`lift`, `formIncl_lift`). With `X, Y` on `Q` (`FormOps.lean`),
`Bₓ = X ∘ lift`, `B_y = Y ∘ lift` are bounded and

  `Δ_ε(t) := -(e^{-2t} Bₓ* Bₓ + B_y* B_y)`  (`lapEps`)

is bounded, self-adjoint (`adjoint_lapEps`) and norm-continuous in `t` (`continuous_lapEps`), with
`⟪u, Δ_ε(t) v⟫ = -(e^{-2t}⟪XJu, XJv⟫ + ⟪YJu, YJv⟫)` (`inner_lapEps`), which is
`⟪Ju, Δ(t) Jv⟫` for `Δ(t) = e^{-2t}X² + Y² - Y` (`X* = -X`, `Y* = 1 - Y`), and
`Δ_ε(0) = J Δ J` (`lapEps_zero`). The mollified flow `V_ε` is the Dyson flow of `(iħ/2)Δ_ε(t)`
(`flowEps`); it is unitary, and Step 2 of the proof of Theorem 1.3R holds for EVERY `a ∈ L²(ℍ)`:
`V_ε(t)* a - a = -(iħ/2) ∫₀ᵗ V_ε(s)* Δ_ε(s) a ds` (`flowEps_duhamel`).
The cutoff of the manuscript, `J_ε = j_ε(Λ)`, is an instance once its bounds are proved.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace ComplexConjugate

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- An admissible spectral cutoff: `r` real, measurable, `r` and `(1 + s) r(s)` bounded. -/
structure Cutoff where
  r : ℝ → ℝ
  meas : Measurable r
  C : ℝ
  bound : ∀ s, |r s| ≤ C
  bound1 : ∀ s, |(1 + s) * r s| ≤ C

namespace Cutoff

variable (χ : Cutoff)

/-- `r` as a complex function. -/
noncomputable def g : ℝ → ℂ := fun s => ((χ.r s : ℝ) : ℂ)

/-- `s r(s)` as a complex function. -/
noncomputable def gS : ℝ → ℂ := fun s => ((s * χ.r s : ℝ) : ℂ)

lemma g_mem : χ.g ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  refine ⟨Complex.measurable_ofReal.comp χ.meas, χ.C, fun s => ?_⟩
  simp only [g, Complex.norm_real, Real.norm_eq_abs]
  exact χ.bound s

lemma gS_mem : χ.gS ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  refine ⟨Complex.measurable_ofReal.comp (measurable_id.mul χ.meas), 2 * χ.C, fun s => ?_⟩
  simp only [gS, Complex.norm_real, Real.norm_eq_abs]
  have h1 := χ.bound s
  have h2 := χ.bound1 s
  have e : s * χ.r s = (1 + s) * χ.r s - χ.r s := by ring
  rw [e]
  calc |(1 + s) * χ.r s - χ.r s| ≤ |(1 + s) * χ.r s| + |χ.r s| := abs_sub _ _
    _ ≤ 2 * χ.C := by linarith

lemma id_mul_g : (fun x : ℝ => (x : ℂ)) * χ.g = χ.gS := by
  funext s; simp [g, gS]

/-- `J = r(-Δ)`. -/
noncomputable def J : L2H →L[ℂ] L2H := (spectralMeasure negLapH_isSelfAdjoint).integral χ.g

/-- `(s r)(-Δ) = -Δ J`. -/
noncomputable def JS : L2H →L[ℂ] L2H := (spectralMeasure negLapH_isSelfAdjoint).integral χ.gS

lemma J_mem_integralDomain (v : L2H) :
    χ.J v ∈ integralDomain (spectralMeasure negLapH_isSelfAdjoint) (fun x : ℝ => (x : ℂ)) :=
  integral_apply_mem_integralDomain _ Complex.measurable_ofReal χ.g_mem
    (by rw [χ.id_mul_g]; exact χ.gS_mem) v

lemma J_mem (v : L2H) : χ.J v ∈ negLapH.domain := by
  rw [A_domain_eq negLapH_isSelfAdjoint]
  exact χ.J_mem_integralDomain v

/-- `-Δ J v = (s r)(-Δ) v`. -/
theorem negLapH_J (v : L2H) : negLapH ⟨χ.J v, χ.J_mem v⟩ = χ.JS v := by
  have e := A_eq_pmapIntegral negLapH_isSelfAdjoint
  have h1 : negLapH ⟨χ.J v, χ.J_mem v⟩
      = pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) (fun x : ℝ => (x : ℂ))
          ⟨χ.J v, χ.J_mem_integralDomain v⟩ :=
    (LinearPMap.ext_iff.mp e).2 (x := χ.J v) (hf := χ.J_mem v) (hg := χ.J_mem_integralDomain v)
  rw [h1]
  have h2 := pmapIntegral_integral_apply (spectralMeasure negLapH_isSelfAdjoint) Complex.measurable_ofReal
    χ.g_mem (by rw [χ.id_mul_g]; exact χ.gS_mem) v
  refine h2.trans ?_
  rw [χ.id_mul_g]
  rfl

lemma conj_g : (fun x => (starRingEnd ℂ) (χ.g x)) = χ.g := by
  funext s; simp [g]

lemma conj_gS : (fun x => (starRingEnd ℂ) (χ.gS x)) = χ.gS := by
  funext s; simp [gS]

theorem adjoint_J : ContinuousLinearMap.adjoint χ.J = χ.J := by
  rw [J, ← ProjectionValuedMeasure.integral_conj _ χ.g_mem, χ.conj_g]

theorem adjoint_JS : ContinuousLinearMap.adjoint χ.JS = χ.JS := by
  rw [JS, ← ProjectionValuedMeasure.integral_conj _ χ.gS_mem, χ.conj_gS]

/-- `R (J + JS) v = J v`, `R = ιι*`: the form-space lift of `J v` is `ι*((1 - Δ) J v)`. -/
theorem formRes_J_add_JS (v : L2H) : formRes negLap (χ.J v + χ.JS v) = χ.J v := by
  obtain ⟨h, hh⟩ := χ.J_mem v
  have heq : (⟨χ.J v, χ.J_mem v⟩ : negLapH.domain) = resEquiv negLap negLap_hasDenseDomain h :=
    Subtype.ext (by rw [coe_resEquiv]; exact hh.symm)
  have hS : negLapH ⟨χ.J v, χ.J_mem v⟩ = h - formRes negLap h := by
    rw [heq]
    exact friedrichsExt_apply negLap negLap_hasDenseDomain h
  rw [χ.negLapH_J] at hS
  have hh' : formRes negLap h = χ.J v := hh
  have : χ.J v + χ.JS v = h := by rw [hS, hh']; abel
  rw [this, hh']

/-- The lift `ι*((1 - Δ) J ·) : L² → Q` of `J`. -/
noncomputable def lift : L2H →L[ℂ] FormSpace negLap := formLift.comp (χ.J + χ.JS)

theorem formIncl_lift (v : L2H) : formIncl negLap (χ.lift v) = χ.J v :=
  χ.formRes_J_add_JS v

/-- `Bₓ = X J`, `B_y = Y J` as bounded operators. -/
noncomputable def Bx : L2H →L[ℂ] L2H := (formVec 1 (Or.inl rfl)).comp χ.lift
noncomputable def By : L2H →L[ℂ] L2H := (formVec Complex.I (Or.inr rfl)).comp χ.lift

/-- `⟪Bₓu, Bₓv⟫ + ⟪B_y u, B_y v⟫ = ⟪u, J(-Δ)J v⟫`. -/
theorem inner_Bx_add_By (u v : L2H) :
    inner ℂ (χ.Bx u) (χ.Bx v) + inner ℂ (χ.By u) (χ.By v) = inner ℂ u ((χ.JS * χ.J) v) := by
  have h := inner_formVec_lift_add ((χ.J + χ.JS) u) ((χ.J + χ.JS) v)
  have h1 : formRes negLap ((χ.J + χ.JS) u) = χ.J u := χ.formRes_J_add_JS u
  have h2 : formRes negLap ((χ.J + χ.JS) v) = χ.J v := χ.formRes_J_add_JS v
  rw [h1, h2] at h
  refine h.trans ?_
  rw [add_apply, add_sub_cancel_left, show (χ.JS * χ.J) v = χ.JS (χ.J v) from rfl,
    ← ContinuousLinearMap.adjoint_inner_left χ.JS (χ.J v) u, χ.adjoint_JS]

/-- **The mollified generator** `Δ_ε(t) = -(e^{-2t} Bₓ*Bₓ + B_y*B_y)`. -/
noncomputable def lapEps (t : ℝ) : L2H →L[ℂ] L2H :=
  -((((Real.exp (-2 * t) : ℝ) : ℂ)) • (ContinuousLinearMap.adjoint χ.Bx * χ.Bx)
    + ContinuousLinearMap.adjoint χ.By * χ.By)

theorem inner_lapEps (t : ℝ) (u v : L2H) :
    inner ℂ u (χ.lapEps t v)
      = -((((Real.exp (-2 * t) : ℝ) : ℂ)) * inner ℂ (χ.Bx u) (χ.Bx v) + inner ℂ (χ.By u) (χ.By v)) := by
  simp only [lapEps, neg_apply, add_apply, smul_apply, inner_neg_right, inner_add_right,
    inner_smul_right, ← ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem adjoint_lapEps (t : ℝ) : ContinuousLinearMap.adjoint (χ.lapEps t) = χ.lapEps t := by
  simp only [lapEps, map_neg, map_add, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal,
    adjoint_mul, ContinuousLinearMap.adjoint_adjoint]

theorem continuous_lapEps : Continuous χ.lapEps := by
  have hc : Continuous fun t : ℝ => (((Real.exp (-2 * t) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h1 : Continuous fun t : ℝ =>
      (((Real.exp (-2 * t) : ℝ) : ℂ)) • (ContinuousLinearMap.adjoint χ.Bx * χ.Bx) :=
    Continuous.smul (M := ℂ) hc continuous_const
  have h : Continuous fun t : ℝ => -((((Real.exp (-2 * t) : ℝ) : ℂ)) • (ContinuousLinearMap.adjoint χ.Bx * χ.Bx)
      + ContinuousLinearMap.adjoint χ.By * χ.By) :=
    (h1.add continuous_const).neg
  exact h

/-- `Δ_ε(0) = J Δ J`. -/
theorem lapEps_zero : χ.lapEps 0 = -(χ.JS * χ.J) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [inner_lapEps, neg_apply, inner_neg_right, ← inner_Bx_add_By]
  simp

/-- The generator `(iħ/2) Δ_ε(t)` of the mollified flow. -/
noncomputable def genEps (hb : ℝ) (t : ℝ) : L2H →L[ℂ] L2H := (Complex.I * (hb : ℂ) / 2) • χ.lapEps t

lemma continuous_genEps (hb : ℝ) : Continuous (χ.genEps hb) := by
  show Continuous fun t => (Complex.I * (hb : ℂ) / 2) • χ.lapEps t
  exact Continuous.smul (M := ℂ) continuous_const χ.continuous_lapEps

lemma adjoint_genEps (hb t : ℝ) : ContinuousLinearMap.adjoint (χ.genEps hb t) = -χ.genEps hb t := by
  rw [genEps, LinearIsometryEquiv.map_smulₛₗ, χ.adjoint_lapEps]
  have hc : (starRingEnd ℂ) (Complex.I * (hb : ℂ) / 2) = -(Complex.I * (hb : ℂ) / 2) := by
    simp [Complex.conj_ofReal, map_ofNat, neg_div]
  rw [hc]
  exact _root_.neg_smul _ _

/-- **The mollified flow** `V_ε(t)`: the Dyson flow of `(iħ/2) Δ_ε(t)`, `V_ε(0) = 1`. -/
noncomputable def flowEps (hb : ℝ) (t : ℝ) : L2H →L[ℂ] L2H := dysonSum (χ.genEps hb) t

theorem flowEps_zero (hb : ℝ) : χ.flowEps hb 0 = 1 := dysonSum_zero _

theorem hasDerivAt_flowEps (hb t : ℝ) :
    HasDerivAt (χ.flowEps hb) (χ.genEps hb t * χ.flowEps hb t) t :=
  hasDerivAt_dysonSum (χ.continuous_genEps hb) t

theorem flowEps_unitary (hb t : ℝ) :
    ContinuousLinearMap.adjoint (χ.flowEps hb t) * χ.flowEps hb t = 1
      ∧ χ.flowEps hb t * ContinuousLinearMap.adjoint (χ.flowEps hb t) = 1 :=
  ⟨adjoint_dysonSum_mul_self (χ.continuous_genEps hb) (χ.adjoint_genEps hb) t,
    dysonSum_mul_adjoint_self (χ.continuous_genEps hb) (χ.adjoint_genEps hb) t⟩

/-- **Step 2 of the proof of Theorem 1.3R**, for every `a ∈ L²(ℍ)`:
`V_ε(t)* a - a = -(iħ/2) ∫₀ᵗ V_ε(s)* Δ_ε(s) a ds`. -/
theorem flowEps_duhamel (hb : ℝ) (a : L2H) (t : ℝ) :
    ContinuousLinearMap.adjoint (χ.flowEps hb t) a - a
      = -(Complex.I * (hb : ℂ) / 2) •
          ∫ s in (0 : ℝ)..t, ContinuousLinearMap.adjoint (χ.flowEps hb s) (χ.lapEps s a) := by
  rw [flowEps, adjoint_dysonSum_sub_eq_integral (χ.continuous_genEps hb) a t,
    ← intervalIntegral.integral_smul]
  congr 1; funext s
  rw [χ.adjoint_genEps, show (ContinuousLinearMap.adjoint (dysonSum (χ.genEps hb) s) * -χ.genEps hb s) a
      = ContinuousLinearMap.adjoint (dysonSum (χ.genEps hb) s) (-(χ.genEps hb s a)) from rfl, genEps,
    smul_apply, map_neg, map_smul]
  exact (_root_.neg_smul _ _).symm

/-! ### The form of `Δ(t)` on test functions -/

/-- `⟪G, y²∂_v²F⟫ = -⟪y∂_vG, y∂_vF⟫` for test functions. -/
lemma inner_toL2_imSqSecond (G F : testFn) (v : ℂ) :
    inner ℂ (toL2 G) (toL2 (⟨fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w v v,
      isTestFn_im_sq_second F.2 v⟩ : testFn))
      = -inner ℂ (toL2 (vfTest v G)) (toL2 (vfTest v F)) := by
  rw [inner_toL2, inner_vf]
  have e : ∀ z : ℍ, conj ((G : ℂ → ℂ) z) * (((z : ℂ).im : ℝ) : ℂ) ^ 2
        * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) z v v
      = (z.im : ℂ) ^ 2 * (fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) z v v * conj ((G : ℂ → ℂ) z)) := by
    intro z; simp only [UpperHalfPlane.coe_im]; ring
  have e' : (fun z : ℍ => conj ((G : ℂ → ℂ) z) * ((⟨fun w => ((w.im : ℝ) : ℂ) ^ 2
      * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w v v, isTestFn_im_sq_second F.2 v⟩ : testFn) : ℂ → ℂ) z)
      = fun z : ℍ => (z.im : ℂ) ^ 2 * (fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) z v v * conj ((G : ℂ → ℂ) z)) := by
    funext z; rw [← e z, mul_assoc]
  rw [e', integral_im_sq_mul (fun w => fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w v v * conj ((G : ℂ → ℂ) w))]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
    have hnot : w ∉ tsupport (G : ℂ → ℂ) := fun h => hw ⟨⟨w, G.2.inside h⟩, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot]; simp)]
  rw [integral_second_mul_conj F.2 G.2 v]
  congr 1; congr 1; funext w; ring

/-- **The form of `Δ(t)` on test functions**:
`⟪G, Δ(t) F⟫ = -(e^{-2t}⟪XG, XF⟫ + ⟪YG, YF⟫)`, the form that defines `Δ_ε(t)` (`inner_lapEps`). -/
theorem inner_lapTL2_form (t : ℝ) (G F : testFn) :
    inner ℂ (toL2 G) (lapTL2 t F)
      = -((((Real.exp (-2 * t) : ℝ) : ℂ)) * inner ℂ (toL2 (vfTest 1 G)) (toL2 (vfTest 1 F))
          + inner ℂ (toL2 (vfTest Complex.I G)) (toL2 (vfTest Complex.I F))) := by
  rw [lapTL2_eq, inner_add_right, inner_smul_right]
  have h1 := inner_toL2_imSqSecond G F 1
  have h2 := inner_toL2_imSqSecond G F Complex.I
  rw [show xxTest F = (⟨fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w 1 1,
      isTestFn_im_sq_second F.2 1⟩ : testFn) from rfl, h1,
    show yyTest F = (⟨fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w Complex.I Complex.I,
      isTestFn_im_sq_second F.2 Complex.I⟩ : testFn) from rfl, h2]
  ring

end Cutoff

end Qschubert
