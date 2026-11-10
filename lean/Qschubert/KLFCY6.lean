import Qschubert.KLFCY5

/-!
# Lemma FC, case `Z = Y`: the remainder kernel and the conclusion

`YE c v = Y e^{-cΛ} v` is a continuous linear map. The remainder kernel
`κ(ν, ν') = -2 (Λ + Λ')⁻¹ φ_a(Λ - Λ') M₂(ν, ν') e^{-γΛ'}` satisfies
`√(w w') |κ| ≤ C₀/(eγ) g(ν - ν')`, `g(x) = (1 + |x|)e^{τ|x|} gam(x/2)`, `C₀ = (2/π²)(1 + π/2) τ` (`kernel_bound_Y`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `v ↦ Y e^{-cΛ} v`. -/
noncomputable def YE (c : ℝ) (hc : 0 < c) : L2H' →L[ℂ] L2H' :=
  (formVec Complex.I (Or.inr rfl)).comp (formLift.comp ((expCut c hc).J + (expCut c hc).JS))

lemma YE_apply (c : ℝ) (hc : 0 < c) (v : L2H') : YE c hc v = domY (expDom c hc v) := by
  show formVec Complex.I (Or.inr rfl) (formLift ((expCut c hc).J v + (expCut c hc).JS v)) = _
  rw [domY, liftDom, expDom, Cutoff.negLapH_J]

lemma continuous_phiA (a : ℝ) : Continuous (phiA a) := by
  unfold phiA
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous (Function.uncurry fun (δ s : ℝ) => Real.exp (s * δ))) 0 a

lemma abs_phiA_le {a δ X : ℝ} (ha : 0 ≤ a) (hδ : |δ| ≤ X) : |phiA a δ| ≤ a * Real.exp (a * X) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := a)
    (f := fun s => Real.exp (s * δ)) (C := Real.exp (a * X)) (fun s hs => ?_)
  · rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ha, mul_comm] at h
    exact h
  · rw [uIoc_of_le ha] at hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have hX : 0 ≤ X := (abs_nonneg _).trans hδ
    calc s * δ ≤ s * |δ| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.1.le
      _ ≤ s * X := mul_le_mul_of_nonneg_left hδ hs.1.le
      _ ≤ a * X := mul_le_mul_of_nonneg_right hs.2 hX

/-- The remainder kernel. -/
noncomputable def kapY (a γ ν ν' : ℝ) : ℝ :=
  -2 * ((LamK ν + LamK ν')⁻¹ * phiA a (LamK ν - LamK ν')) * kerM2 ν ν' * Real.exp (-(γ * LamK ν'))

/-- The majorant. -/
noncomputable def gYk (τ x : ℝ) : ℝ := (1 + |x|) * Real.exp (τ * |x|) * gam (x / 2)

lemma gYk_nonneg (τ x : ℝ) : 0 ≤ gYk τ x := by
  have := gam_pos (x / 2); unfold gYk; positivity

lemma gYk_neg (τ x : ℝ) : gYk τ (-x) = gYk τ x := by
  unfold gYk; rw [abs_neg, neg_div, gam_neg]

lemma measurable_gYk (τ : ℝ) : Measurable (gYk τ) := by
  unfold gYk
  exact ((by fun_prop : Measurable fun x : ℝ => (1 + |x|) * Real.exp (τ * |x|))).mul
    (measurable_gam.comp (by fun_prop))

/-- `P cosh P ≤ (1 + P) sinh P`. -/
lemma mul_cosh_le {P : ℝ} (hP : 0 < P) : P * Real.cosh P ≤ (1 + P) * Real.sinh P := by
  have h1 : P ≤ Real.sinh P := Real.self_le_sinh_iff.2 hP.le
  have h2 : Real.cosh P ≤ Real.sinh P + 1 := by
    have : Real.cosh P - Real.sinh P = Real.exp (-P) := Real.cosh_sub_sinh P
    have h3 : Real.exp (-P) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  nlinarith

/-- **The kernel bound for the `Y` remainder.** -/
theorem kernel_bound_Y {τ a γ ν ν' : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kapY a γ ν ν'|
      ≤ (2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ) * (1 / (Real.exp 1 * γ)) * gYk τ (ν - ν') := by
  have hp := Real.pi_pos
  have hτ : 0 ≤ τ := ha.trans haτ
  set x := ν - ν'
  set p' := (ν + ν') / 2
  set P := Real.pi * p'
  have hp' : 0 < p' := by simp only [p']; positivity
  have hP : 0 < P := by simp only [P]; positivity
  set L := LamK ν
  set L' := LamK ν'
  have hL := LamK_pos ν
  have hL' := LamK_pos ν'
  set σ := L + L'
  have hσ1 : 1 ≤ σ := one_le_lam_sum (ν, ν')
  have hσ2 : 2 * p' ≤ σ := by
    have h1 := le_LamK ν; have h2 := le_LamK ν'
    rw [abs_of_pos hν] at h1; rw [abs_of_pos hν'] at h2
    simp only [p', σ, L, L']; linarith
  have hσ0 : 0 < σ := by linarith
  set G₁ := gam p'
  set G₂ := gam (x / 2)
  have hG1 : 0 < G₁ := gam_pos _
  have hG2 : 0 < G₂ := gam_pos _
  -- (a) the weights
  have hww : Real.sqrt (klW ν) * Real.sqrt (klW ν') ≤ 2 / Real.pi ^ 2 * Real.sqrt (ν * ν') * Real.cosh P := by
    have h0 : 0 ≤ klW ν := klW_nonneg hν.le
    have h0' : 0 ≤ klW ν' := klW_nonneg hν'.le
    have hs := sinh_mul_sinh_le (Real.pi * ν) (Real.pi * ν')
    rw [show (Real.pi * ν + Real.pi * ν') / 2 = P by simp only [P, p']; ring] at hs
    have hnn : 0 ≤ ν * ν' := by positivity
    refine (pow_le_pow_iff_left₀ (by positivity) (by have := Real.cosh_pos P; positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h0, Real.sq_sqrt h0', Real.sq_sqrt hnn]
    unfold klW
    have e : 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * (2 / Real.pi ^ 2 * ν' * Real.sinh (Real.pi * ν'))
        = (2 / Real.pi ^ 2) ^ 2 * (ν * ν') * (Real.sinh (Real.pi * ν) * Real.sinh (Real.pi * ν')) := by ring
    rw [e]; gcongr
  -- (b) `cosh P · gam p' ≤ 1 + P`
  have hb : Real.cosh P * G₁ ≤ 1 + P := by
    simp only [G₁]
    rw [gam_of_ne hp'.ne', show Real.pi * p' = P from rfl]
    have hs : 0 < Real.sinh P := Real.sinh_pos_iff.2 hP
    rw [← mul_div_assoc, div_le_iff₀ hs]
    linarith [mul_cosh_le hP]
  -- (c), (d), (e), (f)
  have hc : (1 + P) * σ⁻¹ ≤ 1 + Real.pi / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hσ0]
    have : P ≤ Real.pi / 2 * σ := by
      simp only [P]; nlinarith
    linarith
  have hd : Real.sqrt (ν * ν') ≤ (1 + |x|) * L' := by
    have h2 : Real.sqrt (ν * ν') ≤ (ν + ν') / 2 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (ν - ν')]
    have h3 := le_LamK ν'; rw [abs_of_pos hν'] at h3
    have h4 := half_le_LamK ν'
    have h5 : (ν - ν') / 2 ≤ |x| * L' := by
      simp only [x]
      nlinarith [le_abs_self (ν - ν'), abs_nonneg (ν - ν')]
    simp only [x] at *; nlinarith
  have he : L' * Real.exp (-(γ * L')) ≤ 1 / (Real.exp 1 * γ) := mul_exp_neg_le_inv hγ hL'.le
  have hf : |phiA a (L - L')| ≤ τ * Real.exp (τ * |x|) := by
    have h1 := abs_phiA_le (X := |x|) ha (abs_LamK_sub_le ν ν')
    calc _ ≤ a * Real.exp (a * |x|) := h1
      _ ≤ τ * Real.exp (τ * |x|) := by gcongr
  have hM2 : kerM2 ν ν' = 1 / 2 * G₁ * G₂ := rfl
  have hE := Real.exp_pos (-(γ * L'))
  have habs : |kapY a γ ν ν'| = 2 * (σ⁻¹ * |phiA a (L - L')|) * (1 / 2 * G₁ * G₂) * Real.exp (-(γ * L')) := by
    unfold kapY
    rw [hM2, abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos (inv_pos.2 hσ0),
      abs_of_pos (by positivity : 0 < 1 / 2 * G₁ * G₂), abs_of_pos hE]
  rw [habs]
  have hcp := Real.cosh_pos P
  have hsq0 : 0 ≤ Real.sqrt (ν * ν') := Real.sqrt_nonneg _
  have hφ0 := abs_nonneg (phiA a (L - L'))
  have hx0 := abs_nonneg x
  unfold gYk
  calc Real.sqrt (klW ν) * Real.sqrt (klW ν') * (2 * (σ⁻¹ * |phiA a (L - L')|) * (1 / 2 * G₁ * G₂) * Real.exp (-(γ * L')))
      ≤ (2 / Real.pi ^ 2 * Real.sqrt (ν * ν') * Real.cosh P) * (2 * (σ⁻¹ * |phiA a (L - L')|) * (1 / 2 * G₁ * G₂) * Real.exp (-(γ * L'))) := by
        gcongr
    _ = 2 / Real.pi ^ 2 * Real.sqrt (ν * ν') * (Real.cosh P * G₁) * σ⁻¹ * |phiA a (L - L')| * G₂ * Real.exp (-(γ * L')) := by ring
    _ ≤ 2 / Real.pi ^ 2 * Real.sqrt (ν * ν') * (1 + P) * σ⁻¹ * |phiA a (L - L')| * G₂ * Real.exp (-(γ * L')) := by gcongr
    _ = 2 / Real.pi ^ 2 * Real.sqrt (ν * ν') * ((1 + P) * σ⁻¹) * |phiA a (L - L')| * G₂ * Real.exp (-(γ * L')) := by ring
    _ ≤ 2 / Real.pi ^ 2 * ((1 + |x|) * L') * (1 + Real.pi / 2) * (τ * Real.exp (τ * |x|)) * G₂ * Real.exp (-(γ * L')) := by
        gcongr
    _ = 2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ * (L' * Real.exp (-(γ * L'))) * ((1 + |x|) * Real.exp (τ * |x|) * G₂) := by ring
    _ ≤ 2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ * (1 / (Real.exp 1 * γ)) * ((1 + |x|) * Real.exp (τ * |x|) * G₂) := by gcongr

/-- `g` is integrable for `τ < π/2`. -/
theorem integrable_gYk {τ : ℝ} (hτ : τ < Real.pi / 2) : Integrable (gYk τ) := by
  have hp := Real.pi_pos
  set δ : ℝ := Real.pi / 2 - τ
  have hδ : 0 < δ := by simp only [δ]; linarith
  set K₁ : ℝ := 1 + 4 / δ
  set K₂ : ℝ := 1 + 2 * Real.pi / δ
  have hsech : Integrable fun x : ℝ => (Real.cosh (δ / 2 * x))⁻¹ := integrable_inv_cosh.comp_mul_left' (by positivity)
  refine (hsech.const_mul (4 * K₁ * K₂)).mono' (measurable_gYk τ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gYk_nonneg τ x)]
  have hx := abs_nonneg x
  set y : ℝ := δ * |x| / 4
  have hy0 : 0 ≤ y := by positivity
  have hxy : |x| = 4 / δ * y := by simp only [y]; field_simp
  have h1 : 1 + |x| ≤ K₁ * Real.exp y := by
    have h := Real.add_one_le_exp y
    have hK : 0 < 4 / δ := by positivity
    calc 1 + |x| = 1 + 4 / δ * y := by rw [← hxy]
      _ ≤ K₁ * (y + 1) := by simp only [K₁]; nlinarith
      _ ≤ K₁ * Real.exp y := by gcongr
  have h2 : 1 + Real.pi * |x / 2| ≤ K₂ * Real.exp y := by
    have h := Real.add_one_le_exp y
    have e : Real.pi * |x / 2| = 2 * Real.pi / δ * y := by
      rw [abs_div, abs_two]; simp only [y]; field_simp; ring
    have hK : 0 < 2 * Real.pi / δ := by positivity
    calc 1 + Real.pi * |x / 2| = 1 + 2 * Real.pi / δ * y := by rw [e]
      _ ≤ K₂ * (y + 1) := by simp only [K₂]; nlinarith
      _ ≤ K₂ * Real.exp y := by gcongr
  have hG := gam_le (x / 2)
  have eπ : Real.pi * |x / 2| = Real.pi / 2 * |x| := by rw [abs_div, abs_two]; ring
  have hcd : Real.cosh (δ / 2 * x) ≤ Real.exp (δ / 2 * |x|) := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      have : Real.exp (-(δ / 2 * x)) ≤ Real.exp (δ / 2 * x) := Real.exp_le_exp.2 (by nlinarith)
      linarith
    · rw [abs_of_neg h]
      have : Real.exp (δ / 2 * x) ≤ Real.exp (-(δ / 2 * x)) := Real.exp_le_exp.2 (by nlinarith)
      have e : δ / 2 * -x = -(δ / 2 * x) := by ring
      rw [e]; linarith
  have hch := Real.cosh_pos (δ / 2 * x)
  have hinv : Real.exp (-(δ / 2 * |x|)) ≤ (Real.cosh (δ / 2 * x))⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ hch hcd
  have hK1 : 0 < K₁ := by simp only [K₁]; positivity
  have hK2 : 0 < K₂ := by simp only [K₂]; positivity
  have hEy := Real.exp_pos y
  have hG0 := gam_pos (x / 2)
  have hexp : Real.exp (τ * |x|) * Real.exp (-(Real.pi * |x / 2|)) * (Real.exp y * Real.exp y) = Real.exp (-(δ / 2 * |x|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, eπ]
    congr 1; simp only [y, δ]; ring
  unfold gYk
  calc (1 + |x|) * Real.exp (τ * |x|) * gam (x / 2)
      ≤ (K₁ * Real.exp y) * Real.exp (τ * |x|) * (4 * (K₂ * Real.exp y) * Real.exp (-(Real.pi * |x / 2|))) := by
        gcongr
        exact hG.trans (by gcongr)
    _ = 4 * K₁ * K₂ * (Real.exp (τ * |x|) * Real.exp (-(Real.pi * |x / 2|)) * (Real.exp y * Real.exp y)) := by ring
    _ = 4 * K₁ * K₂ * Real.exp (-(δ / 2 * |x|)) := by rw [hexp]
    _ ≤ 4 * K₁ * K₂ * (Real.cosh (δ / 2 * x))⁻¹ := by gcongr

/-! ### Kernel operators on `L²(dk ⊗ w dν)` and their pairing with products -/

lemma measurable_kapY (a γ : ℝ) : Measurable fun q : ℝ × ℝ => kapY a γ q.1 q.2 := by
  have h1 : Continuous fun q : ℝ × ℝ => LamK q.1 := continuous_LamK.comp continuous_fst
  have h2 : Continuous fun q : ℝ × ℝ => LamK q.2 := continuous_LamK.comp continuous_snd
  have hinv : Continuous fun q : ℝ × ℝ => (LamK q.1 + LamK q.2)⁻¹ :=
    (h1.add h2).inv₀ (fun q => ne_of_gt (lt_of_lt_of_le one_pos (one_le_lam_sum q)))
  have hφ : Continuous fun q : ℝ × ℝ => phiA a (LamK q.1 - LamK q.2) := (continuous_phiA a).comp (h1.sub h2)
  unfold kapY
  exact (((continuous_const.mul (hinv.mul hφ)).measurable).mul measurable_kerM2).mul
    ((Real.continuous_exp.comp ((continuous_const.mul h2).neg)).measurable)

section generic

variable {κ : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {C : ℝ}

/-- The fiberwise kernel operator. -/
noncomputable def TT (κ : ℝ → ℝ → ℝ) (V : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := kerOp κ (fun ν' => V (p.1, ν')) p.2

lemma stronglyMeasurable_TT (hκ : Measurable fun q : ℝ × ℝ => κ q.1 q.2) {V : ℝ × ℝ → ℂ} (hV : StronglyMeasurable V) :
    StronglyMeasurable (TT κ V) := by
  set F : (ℝ × ℝ) × ℝ → ℂ := fun q => (κ q.1.2 q.2 : ℂ) * ((klW q.2 : ℂ) * V (q.1.1, q.2))
  have m1 : Measurable fun q : (ℝ × ℝ) × ℝ => κ q.1.2 q.2 :=
    hκ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have m2 : Measurable fun q : (ℝ × ℝ) × ℝ => klW q.2 := (continuous_klW.comp continuous_snd).measurable
  have m3 : Measurable fun q : (ℝ × ℝ) × ℝ => V (q.1.1, q.2) :=
    hV.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hF : StronglyMeasurable F :=
    ((Complex.measurable_ofReal.comp m1).mul ((Complex.measurable_ofReal.comp m2).mul m3)).stronglyMeasurable
  exact hF.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

/-- The Schur bound on `L²(dk ⊗ w dν)`. -/
theorem lintegral_TT_le (hκ : Measurable fun q : ℝ × ℝ => κ q.1 q.2) (hg : Measurable g) (hC : 0 ≤ C)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    {V : ℝ × ℝ → ℂ} (hV : StronglyMeasurable V) :
    ∫⁻ p, ‖TT κ V p‖ₑ ^ 2 ∂muU
      ≤ (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x)) ^ 2 * ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU := by
  have hVmeas : Measurable fun p : ℝ × ℝ => ‖V p‖ₑ ^ 2 := hV.measurable.enorm.pow_const (2 : ℕ)
  have eV : ∫⁻ p, ‖V p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖V (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hVmeas.aemeasurable
  have hEm := stronglyMeasurable_TT hκ hV
  have hEm3 : Measurable fun p : ℝ × ℝ => ‖TT κ V p‖ₑ ^ 2 := hEm.measurable.enorm.pow_const (2 : ℕ)
  have e : ∫⁻ p, ‖TT κ V p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖TT κ V (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hEm3.aemeasurable
  rw [e, eV, ← lintegral_const_mul _ hVmeas.lintegral_prod_right']
  refine lintegral_mono fun k => ?_
  have hVk : Measurable fun ν' => V (k, ν') := hV.measurable.comp (measurable_prodMk_left (x := k))
  have hB := kerOp_bound (κ := κ) (a := fun ν' => V (k, ν')) hg hC hb hVk
  have hm : Measurable fun ν => ‖TT κ V (k, ν)‖ₑ ^ 2 :=
    (hEm.measurable.comp (measurable_prodMk_left (x := k))).enorm.pow_const (2 : ℕ)
  rw [lintegral_wNu_eq hm]
  exact hB

lemma lintegral_sq_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (h : MemLp f 2 μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hs := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  have h2 := hs.lintegral_lt_top
  convert h2 using 2
  funext x
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The adjoint amplitude. -/
noncomputable def rA (κ : ℝ → ℝ → ℝ) (A : ℝ → ℂ) : ℝ → ℂ := kerOp (fun ν ν' => κ ν' ν) A

lemma memLp_rA (hκ : Measurable fun q : ℝ × ℝ => κ q.1 q.2) (hg : Measurable g) (hC : 0 ≤ C)
    (hgfin : ∫⁻ x, ENNReal.ofReal (g x) < ⊤)
    (hb' : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν' ν| ≤ C * g (ν - ν'))
    {A : ℝ → ℂ} (hA : IsKTest A) : MemLp (rA κ A) 2 wNu := by
  have hm : StronglyMeasurable (rA κ A) := by
    set F : ℝ × ℝ → ℂ := fun q => (κ q.2 q.1 : ℂ) * ((klW q.2 : ℂ) * A q.2)
    have m1 : Measurable fun q : ℝ × ℝ => κ q.2 q.1 := hκ.comp (measurable_snd.prodMk measurable_fst)
    have m2 : Measurable fun q : ℝ × ℝ => klW q.2 := (continuous_klW.comp continuous_snd).measurable
    have m3 : Measurable fun q : ℝ × ℝ => A q.2 := hA.continuous.measurable.comp measurable_snd
    have hF : StronglyMeasurable F :=
      ((Complex.measurable_ofReal.comp m1).mul ((Complex.measurable_ofReal.comp m2).mul m3)).stronglyMeasurable
    exact hF.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  refine memLp_of_lintegral_sq_lt_top hm.aestronglyMeasurable ?_
  rw [lintegral_wNu_eq (hm.measurable.enorm.pow_const (2 : ℕ))]
  refine lt_of_le_of_lt (kerOp_bound (κ := fun ν ν' => κ ν' ν) hg hC hb' hA.continuous.measurable) ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfin))
    (lintegral_sq_of_memLp (memLp_wNu hA))

/-- **Fubini for the kernel operator**: `⟨A, T_κ V⟩_w = ⟨r_A, V⟩_w`. -/
theorem fiber_TT (hκ : Measurable fun q : ℝ × ℝ => κ q.1 q.2) (hg : Measurable g) (hC : 0 ≤ C)
    (hgfin : ∫⁻ x, ENNReal.ofReal (g x) < ⊤)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    {A : ℝ → ℂ} (hA : IsKTest A) {V₁ : ℝ → ℂ} (hV₁ : Measurable V₁) (hV₂ : ∫⁻ ν, ‖V₁ ν‖ₑ ^ 2 ∂wNu < ⊤) :
    ∫ ν, (starRingEnd ℂ) (A ν) * kerOp κ V₁ ν ∂wNu = ∫ ν, (starRingEnd ℂ) (rA κ A ν) * V₁ ν ∂wNu := by
  set μz : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ × ℝ → ℂ := fun q => (klW q.1 : ℂ) * (starRingEnd ℂ) (A q.1) * ((κ q.1 q.2 : ℂ) * ((klW q.2 : ℂ) * V₁ q.2))
  have hHm : AEStronglyMeasurable H (μz.prod μz) := by
    have m1 : Measurable fun q : ℝ × ℝ => klW q.1 := (continuous_klW.comp continuous_fst).measurable
    have m2 : Measurable fun q : ℝ × ℝ => klW q.2 := (continuous_klW.comp continuous_snd).measurable
    have m3 : Measurable fun q : ℝ × ℝ => (starRingEnd ℂ) (A q.1) :=
      (Complex.continuous_conj.comp (hA.continuous.comp continuous_fst)).measurable
    exact (((Complex.measurable_ofReal.comp m1).mul m3).mul ((Complex.measurable_ofReal.comp hκ).mul
      ((Complex.measurable_ofReal.comp m2).mul (hV₁.comp measurable_snd)))).aestronglyMeasurable
  have hbil := kerOp_bilin (κ := κ) hg hC hb (a := V₁) (c := A) hV₁ hA.continuous.measurable
  have hfin : ∫⁻ ν in Ioi 0, ∫⁻ ν' in Ioi 0, ENNReal.ofReal (klW ν) * (ENNReal.ofReal (klW ν') *
      ENNReal.ofReal |κ ν ν'|) * (‖V₁ ν'‖ₑ * ‖A ν‖ₑ) < ⊤ := by
    have hR : (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x)) ^ 2 * (∫⁻ ν, ‖A ν‖ₑ ^ 2 ∂wNu) * ∫⁻ ν, ‖V₁ ν‖ₑ ^ 2 ∂wNu < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfin))
        (lintegral_sq_of_memLp (memLp_wNu hA))) hV₂
    have h2 := lt_of_le_of_lt hbil hR
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h2
    simp at h2
  have hHi : Integrable H (μz.prod μz) := by
    refine ⟨hHm, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hHm.enorm]
    refine lt_of_le_of_lt ?_ hfin
    refine setLIntegral_mono' measurableSet_Ioi (fun ν hν => ?_)
    refine setLIntegral_mono' measurableSet_Ioi (fun ν' hν' => ?_)
    have hw := klW_nonneg (le_of_lt (hν : (0 : ℝ) < ν))
    have hw' := klW_nonneg (le_of_lt (hν' : (0 : ℝ) < ν'))
    have eR : ∀ r : ℝ, 0 ≤ r → ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r := fun r hr => by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    have eK : ‖((κ ν ν' : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |κ ν ν'| := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
    simp only [H, enorm_mul, eR _ hw, eR _ hw', eK, RCLike.enorm_conj]
    exact le_of_eq (by ring)
  have e1 := integral_prod H hHi
  have e2 := integral_prod_symm H hHi
  have hL : ∫ ν, (starRingEnd ℂ) (A ν) * kerOp κ V₁ ν ∂wNu = ∫ ν, ∫ ν', H (ν, ν') ∂μz ∂μz := by
    rw [integral_wNu_eq]
    refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
    simp only [H, kerOp]
    rw [MeasureTheory.integral_const_mul]; ring
  have hR : ∫ ν, (starRingEnd ℂ) (rA κ A ν) * V₁ ν ∂wNu = ∫ ν', ∫ ν, H (ν, ν') ∂μz ∂μz := by
    rw [integral_wNu_eq]
    refine integral_congr_ae (Eventually.of_forall fun ν' => ?_)
    simp only [H, rA, kerOp]
    rw [← integral_conj, ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
    congr 1; funext ν
    simp only [map_mul, Complex.conj_ofReal]; ring
  rw [hL, hR, ← e1, e2]

/-- `∫ conj(ψ₁ ⊗ g₁) (ψ₂ ⊗ g₂) dmuU` factorizes. -/
lemma integral_conj_prod (ψ₁ ψ₂ g₁ g₂ : ℝ → ℂ) :
    ∫ p : ℝ × ℝ, (starRingEnd ℂ) (ψ₁ p.1 * g₁ p.2) * (ψ₂ p.1 * g₂ p.2) ∂muU
      = (∫ k, (starRingEnd ℂ) (ψ₁ k) * ψ₂ k) * ∫ ν, (starRingEnd ℂ) (g₁ ν) * g₂ ν ∂wNu := by
  have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := wNu)
    (fun k => (starRingEnd ℂ) (ψ₁ k) * ψ₂ k) (fun ν => (starRingEnd ℂ) (g₁ ν) * g₂ ν)
  rw [← h]
  show ∫ p : ℝ × ℝ, _ ∂((volume : Measure ℝ).prod wNu) = _
  congr 1; funext p
  rw [map_mul]; ring

lemma inner_prod_eq {ψ g : ℝ → ℂ} (hψ : MemLp ψ 2 (volume : Measure ℝ)) (hg : MemLp g 2 wNu) (G : Lp ℂ 2 muU)
    {G' : ℝ × ℝ → ℂ} (hG : (G : ℝ × ℝ → ℂ) =ᵐ[muU] G') :
    inner ℂ ((memLp_prod_mul hψ hg).toLp (fun p : ℝ × ℝ => ψ p.1 * g p.2)) G
      = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (ψ p.1 * g p.2) * G' p ∂muU := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_prod_mul hψ hg).coeFn_toLp, hG] with p h1 h2
  rw [h1, h2, RCLike.inner_apply']

end generic

/-! ### The identity on products -/

section products

variable {a γ τ : ℝ} {φ₁ φ₂ A B₀ : ℝ → ℂ}

/-- The Schur constant for the remainder. -/
noncomputable def CstY (τ γ : ℝ) : ℝ := 2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ * (1 / (Real.exp 1 * γ))

lemma CstY_nonneg (hτ : 0 ≤ τ) (hγ : 0 < γ) : 0 ≤ CstY τ γ := by
  unfold CstY; have := Real.pi_pos; positivity

lemma kapY_bound (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) :
    ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kapY a γ ν ν'| ≤ CstY τ γ * gYk τ (ν - ν') :=
  fun _ _ hν hν' => kernel_bound_Y ha haτ hγ hν hν'

lemma kapY_bound' (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) :
    ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kapY a γ ν' ν| ≤ CstY τ γ * gYk τ (ν - ν') := by
  intro ν ν' hν hν'
  have h := kernel_bound_Y (τ := τ) ha haτ hγ hν' hν
  rw [show ν' - ν = -(ν - ν') by ring, gYk_neg, mul_comm (Real.sqrt (klW ν'))] at h
  exact h

lemma integral_conj_half {X Y : ℝ → ℂ} (hX : IsKTest X) (hY : IsKTest Y) :
    ∫ ν, (starRingEnd ℂ) (X ν) * ((1 / 2 : ℂ) * Y ν + HY Y ν) ∂wNu
      = (1 / 2 : ℂ) * (∫ ν, (starRingEnd ℂ) (X ν) * Y ν ∂wNu) + SS X Y := by
  have i1 : Integrable (fun ν => (starRingEnd ℂ) (X ν) * Y ν) wNu := (memLp_wNu hX).star.integrable_mul (memLp_wNu hY)
  have i2 : Integrable (fun ν => (starRingEnd ℂ) (X ν) * HY Y ν) wNu := (memLp_wNu hX).star.integrable_mul (Lp.memLp _)
  have e : SS X Y = ∫ ν, (starRingEnd ℂ) (X ν) * HY Y ν ∂wNu := by
    unfold SS
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coe_TL hX] with ν h1
    rw [h1, RCLike.inner_apply']
  rw [e, ← MeasureTheory.integral_const_mul, ← integral_add (i1.const_mul _) i2]
  congr 1; funext ν; ring

/-- The pairing of the remainder with test functions. -/
lemma kerOp_pair (hA : IsKTest A) (hB₀ : IsKTest B₀) (ha : 0 ≤ a) :
    ∫ ν, (starRingEnd ℂ) (A ν) * kerOp (kapY a γ) B₀ ν ∂wNu
      = -2 * ∫ p : ℝ × ℝ, (((LamK p.1 + LamK p.2)⁻¹ * phiA a (LamK p.1 - LamK p.2) : ℝ) : ℂ) * Tk A (eL (-γ) B₀) p := by
  have hBγ := hB₀.eL (-γ)
  set Bγ := eL (-γ) B₀
  set F₀ : ℝ × ℝ → ℂ := fun p => (((LamK p.1 + LamK p.2)⁻¹ * phiA a (LamK p.1 - LamK p.2) : ℝ) : ℂ) * Tk A Bγ p
  have hF : Integrable F₀ ((volume : Measure ℝ).prod volume) :=
    ((integrable_GG hA hBγ a).integral_prod_right).congr
      (Eventually.of_forall fun p => integral_GG_slice ha p)
  have e0 : ∫ p : ℝ × ℝ, F₀ p = ∫ ν, ∫ ν', F₀ (ν, ν') := integral_prod _ hF
  have e1 : ∫ ν, ∫ ν', F₀ (ν, ν') = ∫ ν in Ioi (0 : ℝ), ∫ ν', F₀ (ν, ν') :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ν hν => by
      have h0 : aW A ν = 0 := (isKTest_aW hA).eq_zero_of_nonpos (not_lt.1 hν)
      simp [F₀, Tk, h0])).symm
  rw [integral_wNu_eq, e0, e1, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν _ => ?_)
  have e2 : ∫ ν', F₀ (ν, ν') = ∫ ν' in Ioi (0 : ℝ), F₀ (ν, ν') :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ν' hν' => by
      have h0 : aW Bγ ν' = 0 := (isKTest_aW hBγ).eq_zero_of_nonpos (not_lt.1 hν')
      simp [F₀, Tk, h0])).symm
  rw [e2, kerOp, ← mul_assoc, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr 1; funext ν'
  simp only [F₀, Tk, kapY, aW, Bγ, eL, map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem ell_products (hτ : τ < Real.pi / 2) (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) (hb : 0 < a + γ)
    (hφ₁ : MemLp φ₁ 2 (volume : Measure ℝ)) (hA : IsKTest A)
    (hr : MemLp (rA (kapY a γ) A) 2 wNu)
    (hφc : Continuous φ₂) (hφs : HasCompactSupport φ₂) (hφ0 : (0 : ℝ) ∉ tsupport φ₂) (hB₀ : IsKTest B₀) :
    inner ℂ ((memLp_prod_mul hφ₁ (memLp_wNu (hA.eL a))).toLp (fun p : ℝ × ℝ => φ₁ p.1 * eL a A p.2))
        (klU (YE (a + γ) hb ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₀)).toLp (PsiH φ₂ (aW B₀)))))
      - inner ℂ ((memLp_prod_mul hφ₁ (memLp_wNu hA)).toLp (fun p : ℝ × ℝ => φ₁ p.1 * A p.2))
        (klU (YE γ hγ ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₀)).toLp (PsiH φ₂ (aW B₀)))))
      - inner ℂ ((memLp_prod_mul hφ₁ hr).toLp (fun p : ℝ × ℝ => φ₁ p.1 * rA (kapY a γ) A p.2))
        (klU ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₀)).toLp (PsiH φ₂ (aW B₀)))) = 0 := by
  set Ψ : L2H' := (memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₀)).toLp (PsiH φ₂ (aW B₀))
  have hΨ : ((klU Ψ : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] Hfun φ₂ B₀ := by
    show ((klU ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₀)).toLp (PsiH φ₂ (aW B₀))) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] _
    rw [klU_PsiH hφc hφs hφ0 hB₀]; exact (memLp_Hfun hφc hφs hφ0 hB₀).coeFn_toLp
  have hex : ∀ (c : ℝ) (hc : 0 < c), ((klU ((expDom c hc Ψ : negLapH.domain) : L2H') : Lp ℂ 2 muU) : ℝ × ℝ → ℂ)
      =ᵐ[muU] Hfun φ₂ (eL (-c) B₀) := by
    intro c hc
    show ((klU ((expCut c hc).J Ψ) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] _
    filter_upwards [klU_expCut hc Ψ, hΨ] with p h1 h2
    rw [h1, h2]
    simp only [Hfun, eL, neg_mul]
    ring
  have hY : ∀ (c : ℝ) (hc : 0 < c), ((klU (YE c hc Ψ) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ)
      =ᵐ[muU] fun p => φ₂ p.1 * ((1 / 2 : ℂ) * eL (-c) B₀ p.2 + HY (eL (-c) B₀) p.2) := by
    intro c hc
    rw [YE_apply]
    exact klU_domY_Hfun hφc hφs (hB₀.eL (-c)) _ (hex c hc) _ (HY_spec1 (hB₀.eL (-c)))
  rw [inner_prod_eq hφ₁ (memLp_wNu (hA.eL a)) _ (hY (a + γ) hb), inner_prod_eq hφ₁ (memLp_wNu hA) _ (hY γ hγ),
    inner_prod_eq hφ₁ hr _ hΨ]
  have t1 := integral_conj_prod φ₁ φ₂ (eL a A) (fun ν => (1 / 2 : ℂ) * eL (-(a + γ)) B₀ ν + HY (eL (-(a + γ)) B₀) ν)
  have t2 := integral_conj_prod φ₁ φ₂ A (fun ν => (1 / 2 : ℂ) * eL (-γ) B₀ ν + HY (eL (-γ) B₀) ν)
  have t3 : ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * rA (kapY a γ) A p.2) * Hfun φ₂ B₀ p ∂muU
      = (∫ k, (starRingEnd ℂ) (φ₁ k) * φ₂ k) * ∫ ν, (starRingEnd ℂ) (rA (kapY a γ) A ν) * B₀ ν ∂wNu :=
    integral_conj_prod φ₁ φ₂ (rA (kapY a γ) A) B₀
  rw [t1, t2, t3, integral_conj_half (hA.eL a) (hB₀.eL _), integral_conj_half hA (hB₀.eL _)]
  have hBb : eL (-(a + γ)) B₀ = eL (-a) (eL (-γ) B₀) := by rw [eL_eL]; congr 1; ring
  have hJ : ∫ ν, (starRingEnd ℂ) (eL a A ν) * eL (-(a + γ)) B₀ ν ∂wNu
      = ∫ ν, (starRingEnd ℂ) (A ν) * eL (-γ) B₀ ν ∂wNu := by
    congr 1; funext ν
    simp only [eL, map_mul, Complex.conj_ofReal]
    have e : Real.exp (a * LamK ν) * Real.exp (-(a + γ) * LamK ν) = Real.exp (-γ * LamK ν) := by
      rw [← Real.exp_add]; congr 1; ring
    have e' : ((Real.exp (a * LamK ν) : ℝ) : ℂ) * ((Real.exp (-(a + γ) * LamK ν) : ℝ) : ℂ) = ((Real.exp (-γ * LamK ν) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, e]
    linear_combination ((starRingEnd ℂ) (A ν) * B₀ ν) * e'
  have hg : ∫⁻ x, ENNReal.ofReal (gYk τ x) < ⊤ := (integrable_gYk hτ).lintegral_lt_top
  have hτ0 : 0 ≤ τ := ha.trans haτ
  have hI3 := fiber_TT (measurable_kapY a γ) (measurable_gYk τ) (CstY_nonneg hτ0 hγ) hg (kapY_bound ha haτ hγ) hA
    hB₀.continuous.measurable (lintegral_sq_of_memLp (memLp_wNu hB₀))
  have hD := duhamel_SS hA (hB₀.eL (-γ)) ha
  rw [← hBb] at hD
  rw [hJ, ← hI3, kerOp_pair hA hB₀ ha]
  linear_combination (∫ k, (starRingEnd ℂ) (φ₁ k) * φ₂ k) * hD

end products

/-! ### Conclusion: Lemma FC for `Y` -/

section final

variable {a γ τ : ℝ}

/-- The identity on products extends to every `v` by density. -/
theorem ell_all (hτ : τ < Real.pi / 2) (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) (hb : 0 < a + γ)
    {φ₁ A : ℝ → ℂ} (hφ₁ : MemLp φ₁ 2 (volume : Measure ℝ)) (hA : IsKTest A)
    (hr : MemLp (rA (kapY a γ) A) 2 wNu) (v : L2H') :
    inner ℂ ((memLp_prod_mul hφ₁ (memLp_wNu (hA.eL a))).toLp (fun p : ℝ × ℝ => φ₁ p.1 * eL a A p.2)) (klU (YE (a + γ) hb v))
      = inner ℂ ((memLp_prod_mul hφ₁ (memLp_wNu hA)).toLp (fun p : ℝ × ℝ => φ₁ p.1 * A p.2)) (klU (YE γ hγ v))
        + inner ℂ ((memLp_prod_mul hφ₁ hr).toLp (fun p : ℝ × ℝ => φ₁ p.1 * rA (kapY a γ) A p.2)) (klU v) := by
  set G₁ := (memLp_prod_mul hφ₁ (memLp_wNu (hA.eL a))).toLp (fun p : ℝ × ℝ => φ₁ p.1 * eL a A p.2)
  set G₀ := (memLp_prod_mul hφ₁ (memLp_wNu hA)).toLp (fun p : ℝ × ℝ => φ₁ p.1 * A p.2)
  set G₂ := (memLp_prod_mul hφ₁ hr).toLp (fun p : ℝ × ℝ => φ₁ p.1 * rA (kapY a γ) A p.2)
  let ℓ : L2H' →L[ℂ] ℂ := (innerSL ℂ G₁).comp (klU.comp (YE (a + γ) hb))
    - (innerSL ℂ G₀).comp (klU.comp (YE γ hγ)) - (innerSL ℂ G₂).comp klU
  have hℓ : ∀ x, ℓ x = inner ℂ G₁ (klU (YE (a + γ) hb x)) - inner ℂ G₀ (klU (YE γ hγ x)) - inner ℂ G₂ (klU x) :=
    fun x => rfl
  set g : L2H' := (InnerProductSpace.toDual ℂ L2H').symm ℓ
  have hg : ∀ x, inner ℂ g x = ℓ x := fun x => InnerProductSpace.toDual_symm_apply
  have h0 : klU g = 0 := eq_zero_of_inner_Hfun (fun φ h hφc hφs hφ0 hh => by
    rw [← klU_PsiH hφc hφs hφ0 hh, ← klUi_apply, ← klUi_apply, klUi.inner_map_map, ← inner_conj_symm, hg, hℓ,
      ell_products hτ ha haτ hγ hb hφ₁ hA hr hφc hφs hφ0 hh, map_zero])
  have g0 : g = 0 := by
    have := norm_klU g
    rw [h0, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  have h1 := hg v
  rw [g0, inner_zero_left, hℓ] at h1
  linear_combination -h1

/-- **Core form of Lemma FC for `Y`.** -/
theorem fc_Y_core (hτ : τ < Real.pi / 2) (ha : 0 ≤ a) (haτ : a ≤ τ) (hγ : 0 < γ) (hb : 0 < a + γ) (v : L2H') :
    ∃ h : domY (expDom (a + γ) hb v) ∈ (expLambda a).domain,
      ‖expLambda a ⟨domY (expDom (a + γ) hb v), h⟩‖ ≤ (2 / γ + CstY τ γ * ∫ x, gYk τ x) * ‖v‖ := by
  have hτ0 : 0 ≤ τ := ha.trans haτ
  set κ := kapY a γ
  set V : Lp ℂ 2 muU := klU v
  have hVm : StronglyMeasurable (V : ℝ × ℝ → ℂ) := Lp.stronglyMeasurable V
  set C := CstY τ γ
  have hC0 : 0 ≤ C := CstY_nonneg hτ0 hγ
  have hκm := measurable_kapY a γ
  have hgm := measurable_gYk τ
  have hgfin : ∫⁻ x, ENNReal.ofReal (gYk τ x) < ⊤ := (integrable_gYk hτ).lintegral_lt_top
  have hb1 := kapY_bound (τ := τ) ha haτ hγ
  have hb2 := kapY_bound' (τ := τ) ha haτ hγ
  have hL := lintegral_TT_le hκm hgm hC0 hb1 hVm
  set I : ℝ := ∫ x, gYk τ x
  have hI0 : 0 ≤ I := integral_nonneg fun x => gYk_nonneg τ x
  have hIg : ∫⁻ x, ENNReal.ofReal (gYk τ x) = ENNReal.ofReal I :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_gYk hτ) (Eventually.of_forall fun x => gYk_nonneg τ x)).symm
  have hVn : ∫⁻ p, ‖(V : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [lintegral_enorm_sq_eq, norm_klU]
  rw [hIg, hVn] at hL
  have hTfin : ∫⁻ p, ‖TT κ V p‖ₑ ^ 2 ∂muU < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top (ENNReal.pow_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top)
  have m𝒯 : MemLp (TT κ V) 2 muU :=
    memLp_of_lintegral_sq_lt_top (stronglyMeasurable_TT hκm hVm).aestronglyMeasurable hTfin
  set Z₁ : Lp ℂ 2 muU := klU (YE γ hγ v)
  set 𝒯L : Lp ℂ 2 muU := m𝒯.toLp (TT κ V)
  set E : Lp ℂ 2 muU := Z₁ + 𝒯L
  set H : Lp ℂ 2 muU := klU (YE (a + γ) hb v)
  have hEae : (E : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => (Z₁ : ℝ × ℝ → ℂ) p + TT κ V p := by
    filter_upwards [Lp.coeFn_add Z₁ 𝒯L, m𝒯.coeFn_toLp] with p h1 h2
    rw [h1]; simp only [Pi.add_apply]; rw [h2]
  -- the identity against products
  have hkey : ∀ {φ₁ A : ℝ → ℂ} (hφ₁ : MemLp φ₁ 2 (volume : Measure ℝ)) (hA : IsKTest A),
      ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * eL a A p.2) * H p ∂muU
        = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * E p ∂muU := by
    intro φ₁ A hφ₁ hA
    have hr := memLp_rA hκm hgm hC0 hgfin hb2 hA
    have hall := ell_all hτ ha haτ hγ hb hφ₁ hA hr v
    rw [inner_prod_eq hφ₁ (memLp_wNu (hA.eL a)) _ (EventuallyEq.refl _ _),
      inner_prod_eq hφ₁ (memLp_wNu hA) _ (EventuallyEq.refl _ _),
      inner_prod_eq hφ₁ hr _ (EventuallyEq.refl _ _)] at hall
    have mP := memLp_prod_mul hφ₁ (memLp_wNu hA)
    have mR := memLp_prod_mul hφ₁ hr
    have I1 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (φ₁ p.1 * rA κ A p.2) * V p) ((volume : Measure ℝ).prod wNu) :=
      mR.star.integrable_mul (Lp.memLp V)
    have I2 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (φ₁ p.1 * A p.2) * TT κ V p) ((volume : Measure ℝ).prod wNu) :=
      mP.star.integrable_mul m𝒯
    have I3 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (φ₁ p.1 * A p.2) * Z₁ p) muU :=
      mP.star.integrable_mul (Lp.memLp Z₁)
    have e1 : ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * rA κ A p.2) * V p ∂muU
        = ∫ k, ∫ ν, (starRingEnd ℂ) (φ₁ k * rA κ A ν) * V (k, ν) ∂wNu := integral_prod _ I1
    have e2 : ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * TT κ V p ∂muU
        = ∫ k, ∫ ν, (starRingEnd ℂ) (φ₁ k * A ν) * TT κ V (k, ν) ∂wNu := integral_prod _ I2
    have hfib : ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * rA κ A p.2) * V p ∂muU
        = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * TT κ V p ∂muU := by
      rw [e1, e2]
      refine integral_congr_ae ?_
      filter_upwards [ae_fiber_lintegral_lt_top hVm (lintegral_enorm_sq_lt_top V)] with k hk
      have hF : ∫ ν, (starRingEnd ℂ) (A ν) * kerOp κ (fun ν' => V (k, ν')) ν ∂wNu
          = ∫ ν, (starRingEnd ℂ) (rA κ A ν) * V (k, ν) ∂wNu :=
        fiber_TT hκm hgm hC0 hgfin hb1 hA (hVm.measurable.comp (measurable_prodMk_left (x := k))) hk
      have l1 : ∫ ν, (starRingEnd ℂ) (φ₁ k * rA κ A ν) * V (k, ν) ∂wNu
          = (starRingEnd ℂ) (φ₁ k) * ∫ ν, (starRingEnd ℂ) (rA κ A ν) * V (k, ν) ∂wNu := by
        rw [← MeasureTheory.integral_const_mul]; congr 1; funext ν; rw [map_mul]; ring
      have l2 : ∫ ν, (starRingEnd ℂ) (φ₁ k * A ν) * TT κ V (k, ν) ∂wNu
          = (starRingEnd ℂ) (φ₁ k) * ∫ ν, (starRingEnd ℂ) (A ν) * kerOp κ (fun ν' => V (k, ν')) ν ∂wNu := by
        rw [← MeasureTheory.integral_const_mul]; congr 1; funext ν; rw [map_mul, TT]; ring
      rw [l1, l2, hF]
    have hsplit : ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * E p ∂muU
        = (∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * Z₁ p ∂muU)
          + ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ₁ p.1 * A p.2) * TT κ V p ∂muU := by
      rw [← integral_add I3 I2]
      refine integral_congr_ae ?_
      filter_upwards [hEae] with p hp
      rw [hp]; ring
    rw [hsplit, ← hfib]
    exact hall
  -- `H = e^{-aΛ} E`
  set E' : ℝ × ℝ → ℂ := fun p => ((Real.exp (-(a * LamK p.2)) : ℝ) : ℂ) * E p
  have mE' : MemLp E' 2 muU := by
    refine (Lp.memLp E).of_le ?_ (Eventually.of_forall fun p => ?_)
    · exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_LamK.comp continuous_snd)).neg))).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable E)
    · simp only [E']
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
      have := LamK_pos p.2
      nlinarith
  have hHE : H = mE'.toLp E' := by
    refine sub_eq_zero.1 (eq_zero_of_inner_Hfun (fun φ h hφc hφs hφ0 hh => ?_))
    have hφ2 := memLp_two_phi hφc hφs
    have hAh : IsKTest (eL (-a) h) := hh.eL (-a)
    have hk := hkey hφ2 hAh
    have heL : eL a (eL (-a) h) = h := by rw [eL_eL, add_neg_cancel, eL_zero]
    rw [heL] at hk
    have i1 : inner ℂ ((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)) H
        = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ p.1 * h p.2) * H p ∂muU :=
      inner_prod_eq hφ2 (memLp_wNu hh) H (EventuallyEq.refl _ _)
    have i2 : inner ℂ ((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)) (mE'.toLp E')
        = ∫ p : ℝ × ℝ, (starRingEnd ℂ) (φ p.1 * h p.2) * E' p ∂muU :=
      inner_prod_eq hφ2 (memLp_wNu hh) _ mE'.coeFn_toLp
    rw [inner_sub_right, i1, i2, hk, sub_eq_zero]
    congr 1; funext p
    simp only [E', eL, map_mul, Complex.conj_ofReal, neg_mul]
    ring
  -- domain and norm
  set f : ℝ → ℂ := fun s => ((Real.exp (a * Real.sqrt s) : ℝ) : ℂ)
  have hf : Measurable f :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have hfH : (fun p => f (mKL p) * (H : ℝ × ℝ → ℂ) p) =ᵐ[muU] (E : ℝ × ℝ → ℂ) := by
    rw [hHE]
    filter_upwards [mE'.coeFn_toLp] with p hp
    rw [hp]
    simp only [E']
    have e : f (mKL p) * ((Real.exp (-(a * LamK p.2)) : ℝ) : ℂ) = 1 := by
      show ((Real.exp (a * LamK p.2) : ℝ) : ℂ) * _ = 1
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    linear_combination ((E : ℝ × ℝ → ℂ) p) * e
  have hmem : MemLp (fun p => f (mKL p) * (H : ℝ × ℝ → ℂ) p) 2 muU := (Lp.memLp E).ae_eq hfH.symm
  have hHu : H = klU (domY (expDom (a + γ) hb v)) := by simp only [H, YE_apply]
  have hd : domY (expDom (a + γ) hb v) ∈ (Physicslib4.Spectral.Unbounded.functionalCalculus negLapH_isSelfAdjoint f).domain :=
    (mem_domain_fc_iff hf _).2 (by rw [← hHu]; exact hmem)
  refine ⟨hd, ?_⟩
  have hn := norm_fc_sq hf ⟨_, hd⟩
  change ‖expLambda a ⟨domY (expDom (a + γ) hb v), hd⟩‖ ^ 2 = _ at hn
  set N : ℝ := ‖expLambda a ⟨domY (expDom (a + γ) hb v), hd⟩‖
  have hsq : Integrable (fun p => ‖f (mKL p) * (H : ℝ × ℝ → ℂ) p‖ ^ 2) muU :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hNE : N = ‖E‖ := by
    have e1 : N ^ 2 = ∫ p, ‖f (mKL p) * (H : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU := by
      rw [hn, ← hHu]; congr 1; funext p; rw [norm_mul, mul_pow]
    have h2 : ENNReal.ofReal (N ^ 2) = ENNReal.ofReal (‖E‖ ^ 2) := by
      rw [e1, ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun p => sq_nonneg _),
        ← lintegral_enorm_sq_eq]
      refine lintegral_congr_ae ?_
      filter_upwards [hfH] with p hp
      rw [hp, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    have h3 := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  have hZ : ‖Z₁‖ ≤ 2 / γ * ‖v‖ := by
    simp only [Z₁]
    rw [norm_klU, YE_apply]
    exact (fc_zero hγ v).2.2
  have hT : ‖𝒯L‖ ≤ C * I * ‖v‖ := by
    have h1 : ENNReal.ofReal (‖𝒯L‖ ^ 2) ≤ ENNReal.ofReal ((C * I * ‖v‖) ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      calc ∫⁻ p, ‖(𝒯L : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU = ∫⁻ p, ‖TT κ V p‖ₑ ^ 2 ∂muU :=
            lintegral_congr_ae (m𝒯.coeFn_toLp.mono fun p hp => congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) hp)
        _ ≤ _ := hL
        _ = ENNReal.ofReal ((C * I * ‖v‖) ^ 2) := by
            rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)] at h1
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  calc N = ‖E‖ := hNE
    _ ≤ ‖Z₁‖ + ‖𝒯L‖ := norm_add_le _ _
    _ ≤ 2 / γ * ‖v‖ + C * I * ‖v‖ := add_le_add hZ hT
    _ = _ := by ring

/-- **Lemma FC for `Z = Y`** (`lem:fc`, all `0 ≤ α'' < α'`, `α'' ≤ τ < π/2`):
`Y e^{-α'Λ} v ∈ Dom e^{α''Λ}` and `‖e^{α''Λ} Y e^{-α'Λ} v‖ ≤ C(τ)/(α' - α'') ‖v‖`.
The Lean proof differs from the printed proof (LOG 11:27Z, 11:40Z): Sylvester identity and Duhamel on the core,
no principal value. -/
theorem fc_Y {τ α'' α' : ℝ} (hτ : τ < Real.pi / 2) (h0 : 0 ≤ α'') (h12 : α'' < α') (h2τ : α'' ≤ τ) (v : L2H') :
    ∃ h : domY (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨domY (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖
        ≤ (2 + 2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ / Real.exp 1 * ∫ x, gYk τ x) / (α' - α'') * ‖v‖ := by
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ, 0 < γ ∧ α' = α'' + γ := ⟨α' - α'', by linarith, by ring⟩
  obtain ⟨h, hN⟩ := fc_Y_core hτ h0 h2τ hγ (lt_of_le_of_lt h0 h12) v
  refine ⟨h, hN.trans (le_of_eq ?_)⟩
  rw [add_sub_cancel_left]
  unfold CstY
  field_simp

end final

/-- **Lemma FC** (`lem:fc`): for `τ₀ < π/2` there is `C₁` such that for `Z ∈ {X, Y}` and `0 ≤ α'' < α' ≤ τ₀`,
`Z e^{-α'Λ} v ∈ Dom e^{α''Λ}` and `‖e^{α''Λ} Z e^{-α'Λ} v‖ ≤ C₁/(α' - α'') ‖v‖`. -/
theorem lem_fc {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (α'' α' : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α'), α' ≤ τ₀ → ∀ v : L2H',
      (∃ h : domX (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨domX (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖) ∧
      (∃ h : domY (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨domY (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖) := by
  set c₁ : ℝ := (∫ x, gK τ₀ x) / Real.exp 1
  set c₂ : ℝ := 2 + 2 / Real.pi ^ 2 * (1 + Real.pi / 2) * τ₀ / Real.exp 1 * ∫ x, gYk τ₀ x
  refine ⟨|c₁| + |c₂|, by positivity, fun α'' α' h0 h12 hle v => ?_⟩
  have hτ : α'' ≤ τ₀ := h12.le.trans hle
  have hγ : 0 < α' - α'' := by linarith
  have hv := norm_nonneg v
  constructor
  · obtain ⟨h, hN⟩ := fc_X hτ₀ h0 h12 hτ v
    refine ⟨h, hN.trans ?_⟩
    have e : (∫ x, gK τ₀ x) / (Real.exp 1 * (α' - α'')) = c₁ / (α' - α'') := by
      simp only [c₁]; field_simp
    rw [e]
    have h1 : c₁ ≤ |c₁| + |c₂| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    gcongr
  · obtain ⟨h, hN⟩ := fc_Y hτ₀ h0 h12 hτ v
    refine ⟨h, hN.trans ?_⟩
    have h1 : c₂ ≤ |c₁| + |c₂| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    gcongr

end Qschubert
