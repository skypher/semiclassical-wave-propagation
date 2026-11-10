import Qschubert.EvModStar
import Qschubert.KLFCY3

/-!
# Moving the scattering term from the test function to `f`

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L4 (second part). For a test function `g` on
`(0, ∞)` let `O_g(y) = (1/2π) ∫ ĝ(1/2 + ir) Φ(1/2 + ir) y^{1/2 - ir} dr` (`outO`), the term of `eisR_eq`. For a
function `f` with `y^{-3/2} f ∈ L¹(0, ∞)` whose Mellin transform on the critical line is the integrable function
`Fh`, let `O_f(y) = (1/2π) ∫ Φ(1/2 + ir) Fh(r) y^{1/2 - ir} dr` (`outF`). Then (`transpose_out`)

`∫_0^∞ conj(O_g) f dy/y² = ∫_0^∞ conj(g) O_f dy/y²`.

Proof: Fubini twice (`fubini_powR`), `conj Φ(s) = Φ(conj s)` and `|Φ(1/2 + ir)| = 1`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate

lemma conj_powR (a : ℂ) (y : ℝ) : conj (powR a y) = powR (conj a) y := by
  rw [powR, powR, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

lemma measurable_powR_line (κ ε : ℝ) :
    Measurable fun p : ℝ × ℝ => powR ((κ : ℂ) + ((ε * p.2 : ℝ) : ℂ) * I) p.1 := by
  unfold powR
  have h1 : Measurable fun p : ℝ × ℝ => (κ : ℂ) + ((ε * p.2 : ℝ) : ℂ) * I :=
    measurable_const.add ((Complex.measurable_ofReal.comp (measurable_const.mul measurable_snd)).mul measurable_const)
  have h2 : Measurable fun p : ℝ × ℝ => ((Real.log p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)
  exact Complex.measurable_exp.comp (h1.mul h2)

lemma norm_powR_line (κ ε r y : ℝ) : ‖powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y‖ = ‖powR (κ : ℂ) y‖ := by
  rw [norm_powR, norm_powR]
  simp

/-- **Fubini for the kernel `y^{κ + iεr}`.** -/
theorem fubini_powR {A U : ℝ → ℂ} (κ ε : ℝ) (hA : Integrable A) (hUm : Measurable U)
    (hU : IntegrableOn (fun y => powR (κ : ℂ) y * U y) (Ioi 0)) :
    ∫ y in Ioi (0 : ℝ), (∫ r : ℝ, A r * powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y) * U y
      = ∫ r : ℝ, A r * ∫ y in Ioi (0 : ℝ), powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y * U y := by
  set f : ℝ → ℝ → ℂ := fun y r => A r * powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y * U y with hf
  have hmeas : AEStronglyMeasurable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ((hA.1.comp_snd).mul (measurable_powR_line κ ε).aestronglyMeasurable).mul
      (hUm.comp measurable_fst).aestronglyMeasurable
  have hmaj : Integrable (fun p : ℝ × ℝ => ‖powR (κ : ℂ) p.1 * U p.1‖ * ‖A p.2‖)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := hU.norm.mul_prod hA.norm
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine hmaj.mono' hmeas (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hf]
    rw [norm_mul, norm_mul, norm_powR_line, norm_mul]
    exact le_of_eq (by ring)
  have hswap := integral_integral_swap hint
  have e1 : ∀ y : ℝ, ∫ r : ℝ, f y r = (∫ r : ℝ, A r * powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y) * U y := fun y => by
    simp only [hf]
    rw [integral_mul_const]
  have e2 : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), f y r
      = A r * ∫ y in Ioi (0 : ℝ), powR ((κ : ℂ) + ((ε * r : ℝ) : ℂ) * I) y * U y := fun r => by
    simp only [hf]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  simp_rw [e1, e2] at hswap
  exact hswap

/-- `conj Φ(s) = Φ(conj s)` for the regular `Φ`. -/
lemma scatPhiR_conj (s : ℂ) : scatPhiR (conj s) = conj (scatPhiR s) := by
  by_cases hs : s = 1 / 2
  · have e : conj s = 1 / 2 := by
      rw [hs, map_div₀, map_one, Complex.conj_ofNat]
    rw [e, hs, scatPhiR_half]
    simp
  · have hs' : conj s ≠ 1 / 2 := by
      intro h
      apply hs
      have := congrArg conj h
      rw [Complex.conj_conj, map_div₀, map_one, Complex.conj_ofNat] at this
      exact this
    rw [scatPhiR_eq hs', scatPhiR_eq hs, scatPhi_conj]

/-- The point `1/2 + ir`. -/
noncomputable def critS (r : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + r * I

lemma critS_re (r : ℝ) : (critS r).re = 1 / 2 := by simp [critS]

lemma continuous_critS : Continuous critS := by
  unfold critS
  fun_prop

lemma conj_critS (r : ℝ) : conj (critS r) = critS (-r) := by
  rw [critS, critS, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma norm_scatPhiR_critS (r : ℝ) : ‖scatPhiR (critS r)‖ = 1 := norm_scatPhiR_critical (critS_re r)

lemma continuous_scatPhiR_critS : Continuous fun r : ℝ => scatPhiR (critS r) := by
  rw [continuous_iff_continuousAt]
  intro r
  have hre := critS_re r
  have h0 : critS r ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    norm_num at this
  have h1 : critS r ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    norm_num at this
  have hd := differentiableAt_scatPhiR h0 h1 (scatD_ne_zero (by rw [hre]))
  exact ContinuousAt.comp (g := scatPhiR) (f := critS) hd.continuousAt continuous_critS.continuousAt

/-- `O_g(y) = (1/2π) ∫ ĝ(1/2 + ir) Φ(1/2 + ir) y^{1/2 - ir} dr`. -/
noncomputable def outO (g : ℝ → ℂ) (y : ℝ) : ℂ := (1 / (2 * π) : ℂ) * ∫ r : ℝ, shiftW g y (critS r)

/-- `O_f(y) = (1/2π) ∫ Φ(1/2 + ir) Fh(r) y^{1/2 - ir} dr`. -/
noncomputable def outF (Fh : ℝ → ℂ) (y : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, scatPhiR (critS r) * Fh r * powR (1 - critS r) y

lemma conj_mellT (g : ℝ → ℂ) (s : ℂ) : conj (mellT g s) = mellT (fun y => conj (g y)) (conj s) := by
  rw [mellT, mellT, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_mul, conj_powR, map_sub, map_neg, map_one]

/-- `y^{1/2 ∓ ir} y^{-2} = y^{-3/2 ∓ ir}`. -/
lemma powR_sub_critS_mul {y : ℝ} (hy : 0 < y) (r : ℝ) :
    powR (1 - critS r) y * (((y ^ 2)⁻¹ : ℝ) : ℂ) = powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y := by
  rw [← powR_neg_two hy, ← powR_add]
  congr 1
  rw [critS]
  push_cast
  ring

lemma powR_conj_sub_critS_mul {y : ℝ} (hy : 0 < y) (r : ℝ) :
    conj (powR (1 - critS r) y) * (((y ^ 2)⁻¹ : ℝ) : ℂ) = powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y := by
  rw [conj_powR, ← powR_neg_two hy, ← powR_add]
  congr 1
  rw [map_sub, map_one, conj_critS, critS]
  push_cast
  ring

/-- **The transposition.** -/
theorem transpose_out {g : ℝ → ℂ} (hg : IsKTest g) {f Fh : ℝ → ℂ} (hfm : Measurable f)
    (hf : IntegrableOn (fun y => powR ((-(3 / 2) : ℝ) : ℂ) y * f y) (Ioi 0)) (hFi : Integrable Fh)
    (hmel : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * I) - 1) y * f y = Fh r) :
    ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (outO g y) * f y)
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y) * outF Fh y) := by
  have hπ : conj ((1 / (2 * π) : ℂ)) = (1 / (2 * π) : ℂ) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_ofNat, Complex.conj_ofReal]
  -- the two functions of `r`
  set A₁ : ℝ → ℂ := fun r => conj (mellT g (critS r) * scatPhiR (critS r)) with hA₁
  set A₂ : ℝ → ℂ := fun r => scatPhiR (critS r) * Fh r with hA₂
  have hmc : Continuous fun r : ℝ => mellT g (critS r) := (continuous_mellT hg).comp continuous_critS
  have hmi : Integrable fun r : ℝ => mellT g (critS r) := by
    have := integrable_mellT_line hg (1 / 2)
    exact this
  have hA₁i : Integrable A₁ := by
    refine hmi.norm.mono' (Complex.continuous_conj.comp (hmc.mul continuous_scatPhiR_critS)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    simp only [hA₁]
    rw [RCLike.norm_conj, norm_mul, norm_scatPhiR_critS, mul_one]
  have hA₂i : Integrable A₂ := by
    refine hFi.norm.mono' (continuous_scatPhiR_critS.aestronglyMeasurable.mul hFi.1) (Eventually.of_forall fun r => ?_)
    simp only [hA₂]
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hgc : IsKTest fun y => conj (g y) := hg.conj
  have hUg : IntegrableOn (fun y => powR ((-(3 / 2) : ℝ) : ℂ) y * conj (g y)) (Ioi 0) :=
    (hgc.integrable_powR_mul _).integrableOn
  -- the left side
  have hL : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (outO g y) * f y)
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, A₁ r * Fh (-r) := by
    have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (outO g y) * f y)
        = (1 / (2 * π) : ℂ) * ((∫ r : ℝ, A₁ r * powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y) * f y) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [outO, map_mul, hπ, ← integral_conj, Complex.real_smul]
      have e : ∀ r : ℝ, conj (shiftW g y (critS r)) * (((y ^ 2)⁻¹ : ℝ) : ℂ)
          = A₁ r * powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y := by
        intro r
        simp only [hA₁]
        rw [shiftW, map_mul, mul_assoc, powR_conj_sub_critS_mul hy0]
      have e2 : (∫ r : ℝ, conj (shiftW g y (critS r))) * (((y ^ 2)⁻¹ : ℝ) : ℂ)
          = ∫ r : ℝ, A₁ r * powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y := by
        rw [← integral_mul_const]
        exact integral_congr_ae (Eventually.of_forall e)
      rw [← e2]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, fubini_powR (-(3 / 2)) 1 hA₁i hfm hf]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    have e5 : ∫ y in Ioi (0 : ℝ), powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y * f y = Fh (-r) := by
      rw [← hmel (-r)]
      have e6 : ((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I = -(1 / 2 + ((-r : ℝ) : ℂ) * I) - 1 := by
        push_cast
        ring
      rw [e6]
    show A₁ r * (∫ y in Ioi (0 : ℝ), powR (((-(3 / 2) : ℝ) : ℂ) + ((1 * r : ℝ) : ℂ) * I) y * f y) = A₁ r * Fh (-r)
    rw [e5]
  -- the right side
  have hR : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y) * outF Fh y)
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, A₂ r
          * ∫ y in Ioi (0 : ℝ), powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y * conj (g y) := by
    have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y) * outF Fh y)
        = (1 / (2 * π) : ℂ) * ((∫ r : ℝ, A₂ r * powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y)
          * conj (g y)) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [outF, Complex.real_smul]
      have e2 : (∫ r : ℝ, scatPhiR (critS r) * Fh r * powR (1 - critS r) y) * (((y ^ 2)⁻¹ : ℝ) : ℂ)
          = ∫ r : ℝ, A₂ r * powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y := by
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only [hA₂]
        rw [mul_assoc, powR_sub_critS_mul hy0]
      rw [← e2]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      fubini_powR (U := fun y => conj (g y)) (-(3 / 2)) (-1) hA₂i hgc.continuous.measurable hUg]
  rw [hL, hR]
  congr 1
  -- the substitution `r → -r` and the conjugations
  rw [← integral_neg_eq_self (fun r : ℝ => A₁ r * Fh (-r))]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have e3 : mellT (fun y => conj (g y)) (critS r)
      = ∫ y in Ioi (0 : ℝ), powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y * conj (g y) := by
    have e4 : -critS r - 1 = ((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I := by
      rw [critS]
      push_cast
      ring
    rw [mellT, e4]
  have e7 : conj (mellT g (critS (-r))) = mellT (fun y => conj (g y)) (critS r) := by
    rw [conj_mellT, conj_critS, neg_neg]
  have e8 : conj (scatPhiR (critS (-r))) = scatPhiR (critS r) := by
    rw [← scatPhiR_conj, conj_critS, neg_neg]
  show conj (mellT g (critS (-r)) * scatPhiR (critS (-r))) * Fh (- -r)
    = scatPhiR (critS r) * Fh r
      * ∫ y in Ioi (0 : ℝ), powR (((-(3 / 2) : ℝ) : ℂ) + (((-1) * r : ℝ) : ℂ) * I) y * conj (g y)
  rw [map_mul, e7, e8, e3, neg_neg]
  ring

end Qschubert
