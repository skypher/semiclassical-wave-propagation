import Qschubert.JEps

/-!
# The mollified generator maps into the Friedrichs domain

For a cutoff `χ` with `s² r(s)` also bounded (`hS2`: `gSS ∈ BddMeasurable`):

* `JS v ∈ Dom(-Δ)` with `-Δ JS v = (s² r)(-Δ) v` (`JS_mem`, `negLapH_JS`), as `negLapH_J` one power up;
* `Bₓ = (X ∘ lift₀) ∘ (J + JS)` (`lift₀ = formLift`), so `Bₓ* = (J + JS) ∘ Kₓ`, `Kₓ = (X ∘ lift₀)*`
  (`adjoint_Bx`), likewise `B_y* = (J + JS) ∘ K_y`;
* `Δ_ε(t) = (J + JS) ∘ L_ε(t)` with `L_ε(t) = -(e^{-2t} Kₓ Bₓ + K_y B_y)` (`lapEps_eq`), hence
  `Δ_ε(t) v ∈ Dom(-Δ)` and `-Δ Δ_ε(t) v = (JS + JSS) L_ε(t) v` (`lapEps_mem`, `negLapH_lapEps`): a
  bounded operator, norm-continuous in `t`.
* Schubert's cutoff satisfies `hS2` (`cutoffEps_gSS_mem`): `s² j_ε(√|s|)` is bounded by the
  Gaussian decay of `j_ε`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace ComplexConjugate

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

namespace Cutoff

variable (χ : Cutoff)

/-- `s² r(s)` as a complex function. -/
noncomputable def gSS : ℝ → ℂ := fun s => ((s * (s * χ.r s) : ℝ) : ℂ)

lemma id_mul_gS : (fun x : ℝ => (x : ℂ)) * χ.gS = χ.gSS := by
  funext s; simp [gS, gSS]

/-- `(s² r)(-Δ)`. -/
noncomputable def JSS : L2H →L[ℂ] L2H := (spectralMeasure negLapH_isSelfAdjoint).integral χ.gSS

variable {χ}

lemma JS_mem_integralDomain (hS2 : χ.gSS ∈ BddMeasurable ℝ) (v : L2H) :
    χ.JS v ∈ integralDomain (spectralMeasure negLapH_isSelfAdjoint) (fun x : ℝ => (x : ℂ)) :=
  integral_apply_mem_integralDomain _ Complex.measurable_ofReal χ.gS_mem
    (by rw [χ.id_mul_gS]; exact hS2) v

lemma JS_mem (hS2 : χ.gSS ∈ BddMeasurable ℝ) (v : L2H) : χ.JS v ∈ negLapH.domain := by
  rw [A_domain_eq negLapH_isSelfAdjoint]
  exact JS_mem_integralDomain hS2 v

/-- `-Δ JS v = (s² r)(-Δ) v`. -/
theorem negLapH_JS (hS2 : χ.gSS ∈ BddMeasurable ℝ) (v : L2H) :
    negLapH ⟨χ.JS v, JS_mem hS2 v⟩ = χ.JSS v := by
  have e := A_eq_pmapIntegral negLapH_isSelfAdjoint
  have h1 : negLapH ⟨χ.JS v, JS_mem hS2 v⟩
      = pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) (fun x : ℝ => (x : ℂ))
          ⟨χ.JS v, JS_mem_integralDomain hS2 v⟩ :=
    (LinearPMap.ext_iff.mp e).2 (x := χ.JS v) (hf := JS_mem hS2 v) (hg := JS_mem_integralDomain hS2 v)
  rw [h1]
  have h2 := pmapIntegral_integral_apply (spectralMeasure negLapH_isSelfAdjoint) Complex.measurable_ofReal
    χ.gS_mem (by rw [χ.id_mul_gS]; exact hS2) v
  refine h2.trans ?_
  rw [χ.id_mul_gS]
  rfl

lemma add_mem_dom (hS2 : χ.gSS ∈ BddMeasurable ℝ) (w : L2H) : (χ.J + χ.JS) w ∈ negLapH.domain :=
  negLapH.domain.add_mem (χ.J_mem w) (JS_mem hS2 w)

/-- `-Δ (J + JS) w = (JS + JSS) w`. -/
theorem negLapH_add (hS2 : χ.gSS ∈ BddMeasurable ℝ) (w : L2H) :
    negLapH ⟨(χ.J + χ.JS) w, add_mem_dom hS2 w⟩ = (χ.JS + χ.JSS) w := by
  have e : (⟨(χ.J + χ.JS) w, add_mem_dom hS2 w⟩ : negLapH.domain)
      = ⟨χ.J w, χ.J_mem w⟩ + ⟨χ.JS w, JS_mem hS2 w⟩ := Subtype.ext rfl
  rw [e, LinearPMap.map_add, χ.negLapH_J, negLapH_JS hS2]
  rfl

variable (χ)

/-- `Kₓ = (X ∘ formLift)*`. -/
noncomputable def Kx : L2H →L[ℂ] L2H :=
  ContinuousLinearMap.adjoint ((formVec 1 (Or.inl rfl)).comp formLift)

/-- `K_y = (Y ∘ formLift)*`. -/
noncomputable def Ky : L2H →L[ℂ] L2H :=
  ContinuousLinearMap.adjoint ((formVec Complex.I (Or.inr rfl)).comp formLift)

theorem adjoint_Bx : ContinuousLinearMap.adjoint χ.Bx = (χ.J + χ.JS).comp Kx := by
  have e : χ.Bx = ((formVec 1 (Or.inl rfl)).comp formLift).comp (χ.J + χ.JS) := rfl
  rw [e, ContinuousLinearMap.adjoint_comp, map_add, χ.adjoint_J, χ.adjoint_JS]
  rfl

theorem adjoint_By : ContinuousLinearMap.adjoint χ.By = (χ.J + χ.JS).comp Ky := by
  have e : χ.By = ((formVec Complex.I (Or.inr rfl)).comp formLift).comp (χ.J + χ.JS) := rfl
  rw [e, ContinuousLinearMap.adjoint_comp, map_add, χ.adjoint_J, χ.adjoint_JS]
  rfl

/-- `L_ε(t) = -(e^{-2t} Kₓ Bₓ + K_y B_y)`. -/
noncomputable def Leps (t : ℝ) : L2H →L[ℂ] L2H :=
  -((((Real.exp (-2 * t) : ℝ) : ℂ)) • (Kx.comp χ.Bx) + Ky.comp χ.By)

/-- **`Δ_ε(t) = (J + JS) ∘ L_ε(t)`.** -/
theorem lapEps_eq (t : ℝ) : χ.lapEps t = (χ.J + χ.JS).comp (χ.Leps t) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [lapEps, Leps, χ.adjoint_Bx, χ.adjoint_By, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.comp_apply, map_neg, map_add, map_smul]

lemma continuous_Leps : Continuous χ.Leps := by
  have hc : Continuous fun t : ℝ => (((Real.exp (-2 * t) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h1 : Continuous fun t : ℝ => (((Real.exp (-2 * t) : ℝ) : ℂ)) • (Kx.comp χ.Bx) :=
    Continuous.smul (M := ℂ) hc continuous_const
  exact (h1.add continuous_const).neg

variable {χ}

lemma lapEps_mem (hS2 : χ.gSS ∈ BddMeasurable ℝ) (t : ℝ) (v : L2H) :
    χ.lapEps t v ∈ negLapH.domain := by
  rw [χ.lapEps_eq t]; exact add_mem_dom hS2 _

/-- **`-Δ Δ_ε(t) v = (JS + JSS) L_ε(t) v`**: a bounded operator, continuous in `t`. -/
theorem negLapH_lapEps (hS2 : χ.gSS ∈ BddMeasurable ℝ) (t : ℝ) (v : L2H) :
    negLapH ⟨χ.lapEps t v, lapEps_mem hS2 t v⟩ = ((χ.JS + χ.JSS).comp (χ.Leps t)) v := by
  have e : (⟨χ.lapEps t v, lapEps_mem hS2 t v⟩ : negLapH.domain)
      = ⟨(χ.J + χ.JS) (χ.Leps t v), add_mem_dom hS2 _⟩ :=
    Subtype.ext (show χ.lapEps t v = (χ.J + χ.JS) (χ.Leps t v) by rw [χ.lapEps_eq t]; rfl)
  rw [e, negLapH_add hS2]
  rfl

end Cutoff

/-! ### Schubert's cutoff satisfies the second-moment bound -/

lemma one_add_sq_mul_exp_le' (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * Real.exp (-x / 8) ≤ 256 := by
  have h := Real.add_one_le_exp (x / 16)
  have hpos := Real.exp_pos (x / 8)
  have e8 : Real.exp (x / 8) = Real.exp (x / 16) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e : Real.exp (-x / 8) = (Real.exp (x / 8))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, ← div_eq_mul_inv, div_le_iff₀ hpos, e8]
  have h1 : 1 + x ≤ 16 * (x / 16 + 1) := by linarith
  have h2 : 0 ≤ 1 + x := by linarith
  calc (1 + x) ^ 2 ≤ (16 * (x / 16 + 1)) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = 256 * (x / 16 + 1) ^ 2 := by ring
    _ ≤ 256 * Real.exp (x / 16) ^ 2 := by
        gcongr

namespace MollProfile

variable (P : MollProfile) {ε : ℝ}

/-- **`s² j_ε(√|s|)` is bounded** (so `cutoffEps` satisfies `hS2`). -/
theorem cutoffEps_gSS_mem (hε : 0 < ε) : (P.cutoffEps hε).gSS ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable]
  refine ⟨Complex.measurable_ofReal.comp (measurable_id.mul (measurable_id.mul (P.cutoffEps hε).meas)),
    (4 / ε) ^ 4 + 4 / ε * 256, fun s => ?_⟩
  simp only [Cutoff.gSS, Complex.norm_real, Real.norm_eq_abs]
  show |s * (s * P.jEps ε (√|s|))| ≤ _
  set l := √|s| with hl
  have hls : l ^ 2 = |s| := Real.sq_sqrt (abs_nonneg s)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hj0 := P.jEps_nonneg ε l
  have hj1 := P.jEps_le_one ε l
  have habs : |s * (s * P.jEps ε l)| = l ^ 4 * P.jEps ε l := by
    rw [abs_mul, abs_mul, abs_of_nonneg hj0, ← hls]; ring
  rw [habs]
  have h4 : 0 ≤ (4 / ε) ^ 4 := by positivity
  have h256 : 0 ≤ 4 / ε * 256 := by positivity
  by_cases hbig : 4 / ε ≤ |l|
  · have hd := P.jEps_le_exp hε hbig
    have hx := one_add_sq_mul_exp_le' (l ^ 2) (sq_nonneg l)
    have e : -(l ^ 2) / 8 = -l ^ 2 / 8 := by ring
    rw [e] at hx
    have hle : l ^ 4 ≤ (1 + l ^ 2) ^ 2 := by nlinarith [sq_nonneg l]
    calc l ^ 4 * P.jEps ε l ≤ (1 + l ^ 2) ^ 2 * (4 / ε * Real.exp (-l ^ 2 / 8)) :=
          mul_le_mul hle hd hj0 (by positivity)
      _ = 4 / ε * ((1 + l ^ 2) ^ 2 * Real.exp (-l ^ 2 / 8)) := by ring
      _ ≤ 4 / ε * 256 := mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ (4 / ε) ^ 4 + 4 / ε * 256 := by linarith
  · have hsm : l ≤ 4 / ε := by rw [abs_of_nonneg hl0] at hbig; exact (not_le.1 hbig).le
    have hl4 : l ^ 4 ≤ (4 / ε) ^ 4 := pow_le_pow_left₀ hl0 hsm 4
    calc l ^ 4 * P.jEps ε l ≤ (4 / ε) ^ 4 * 1 := mul_le_mul hl4 hj1 hj0 h4
      _ ≤ (4 / ε) ^ 4 + 4 / ε * 256 := by linarith

end MollProfile

end Qschubert
