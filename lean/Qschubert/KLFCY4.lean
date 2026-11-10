import Qschubert.KLFCY3

/-!
# Lemma FC, case `Z = Y`: the form on exponential curves

`eL c B = e^{cΛ}B`, `mL B = ΛB` keep test functions test functions. `HY B ∈ L²(w)` represents the form:
`⟨A, HY B⟩ = S(wA, wB)` (`HY_spec`), it is linear in `B` (`HY_lin`) and `‖HY B‖ ≤ (5/2)‖e^{Λ}B‖` (`norm_HY_le`).
Curves `s ↦ L(e^{σ s Λ}C)` are differentiable for such `L` (`curve_deriv`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Asymptotics
open scoped ENNReal ContDiff

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

noncomputable def eL (c : ℝ) (B : ℝ → ℂ) (ν : ℝ) : ℂ := ((Real.exp (c * LamK ν) : ℝ) : ℂ) * B ν
noncomputable def mL (B : ℝ → ℂ) (ν : ℝ) : ℂ := (LamK ν : ℂ) * B ν

lemma contDiff_LamK : ContDiff ℝ ∞ LamK := by
  unfold LamK
  exact ContDiff.sqrt (by fun_prop) (fun ν => by positivity)

lemma IsKTest.eL {B : ℝ → ℂ} (hB : IsKTest B) (c : ℝ) : IsKTest (Qschubert.eL c B) :=
  hB.mul_smooth (φ := fun ν => ((Real.exp (c * LamK ν) : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_LamK)))

lemma IsKTest.mL {B : ℝ → ℂ} (hB : IsKTest B) : IsKTest (Qschubert.mL B) :=
  hB.mul_smooth (φ := fun ν => (LamK ν : ℂ)) (Complex.ofRealCLM.contDiff.comp contDiff_LamK)

lemma IsKTest.lin {B₁ B₂ : ℝ → ℂ} (h₁ : IsKTest B₁) (h₂ : IsKTest B₂) (c₁ c₂ : ℂ) :
    IsKTest fun ν => c₁ * B₁ ν + c₂ * B₂ ν :=
  (h₁.mul_smooth (φ := fun _ => c₁) contDiff_const).add (h₂.mul_smooth (φ := fun _ => c₂) contDiff_const)

/-- `B` as an element of `L²(w)` (`0` if `B` is not a test function). -/
noncomputable def TL (B : ℝ → ℂ) : Lp ℂ 2 wNu :=
  open Classical in if hB : IsKTest B then (memLp_wNu hB).toLp B else 0

lemma TL_of {B : ℝ → ℂ} (hB : IsKTest B) : TL B = (memLp_wNu hB).toLp B := by simp [TL, hB]

lemma coe_TL {B : ℝ → ℂ} (hB : IsKTest B) : (TL B : ℝ → ℂ) =ᵐ[wNu] B := by
  rw [TL_of hB]; exact (memLp_wNu hB).coeFn_toLp

lemma TL_lin {B₁ B₂ : ℝ → ℂ} (h₁ : IsKTest B₁) (h₂ : IsKTest B₂) (c₁ c₂ : ℂ) :
    TL (fun ν => c₁ * B₁ ν + c₂ * B₂ ν) = c₁ • TL B₁ + c₂ • TL B₂ := by
  apply Lp.ext
  have hsum := Lp.coeFn_add (c₁ • TL B₁) (c₂ • TL B₂)
  have s1 := Lp.coeFn_smul c₁ (TL B₁)
  have s2 := Lp.coeFn_smul c₂ (TL B₂)
  filter_upwards [coe_TL (h₁.lin h₂ c₁ c₂), coe_TL h₁, coe_TL h₂, hsum, s1, s2] with ν e0 e1 e2 e3 e4 e5
  rw [e0, e3]
  simp only [Pi.add_apply]
  rw [e4, e5]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1, e2]

/-- `klInvD` is linear in the amplitude on test functions. -/
lemma hatA_lin {b₁ b₂ : ℝ → ℂ} (h₁ : IsKTest b₁) (h₂ : IsKTest b₂) (c₁ c₂ : ℂ) (t : ℝ) :
    hatA (fun ν => c₁ * b₁ ν + c₂ * b₂ ν) t = c₁ * hatA b₁ t + c₂ * hatA b₂ t := by
  have i : ∀ {k : ℝ → ℂ}, IsKTest k → Integrable fun ν : ℝ => Complex.exp ((ν : ℂ) * t * I) * k ν := fun hk =>
    ((by fun_prop : Continuous fun ν : ℝ => Complex.exp ((ν : ℂ) * t * I)).mul hk.continuous).integrable_of_hasCompactSupport
      hk.compact.mul_left
  unfold hatA
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← integral_add ((i h₁).const_mul c₁) ((i h₂).const_mul c₂)]
  congr 1; funext ν; ring

/-- `S` is linear in the second amplitude. -/
lemma Sform_lin {a b₁ b₂ : ℝ → ℂ} (ha : IsKTest a) (h₁ : IsKTest b₁) (h₂ : IsKTest b₂) (c₁ c₂ : ℂ) :
    Sform a (fun ν => c₁ * b₁ ν + c₂ * b₂ ν) = c₁ * Sform a b₁ + c₂ * Sform a b₂ := by
  have hK : Continuous fun p : ℝ × ℝ => coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 :=
    (continuous_coshSum.rpow_const (fun p => Or.inl (coshSum_pos p).ne')).mul continuous_cosh_snd
  have hb : ∀ p : ℝ × ℝ, |coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2| ≤ 1 := by
    intro p
    have hσ := coshSum_pos p
    have h0 := Real.cosh_pos p.2
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hσ.le _) h0.le), Real.rpow_neg_one,
      inv_mul_le_iff₀ hσ, mul_one]
    unfold coshSum; linarith [Real.cosh_pos p.1]
  have i1 := integrable_K ha h₁ hK hb
  have i2 := integrable_K ha h₂ hK hb
  rw [Sform_eq ha (h₁.lin h₂ c₁ c₂), Sform_eq ha h₁, Sform_eq ha h₂]
  simp_rw [hatA_lin h₁ h₂ c₁ c₂]
  have e : ∫ p : ℝ × ℝ, ((coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 : ℝ) : ℂ)
        * ((starRingEnd ℂ) (hatA a p.1) * (c₁ * hatA b₁ p.2 + c₂ * hatA b₂ p.2))
      = c₁ * (∫ p : ℝ × ℝ, ((coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b₁ p.2))
        + c₂ * ∫ p : ℝ × ℝ, ((coshSum p ^ (-(1 : ℝ)) * Real.cosh p.2 : ℝ) : ℂ) * ((starRingEnd ℂ) (hatA a p.1) * hatA b₂ p.2) := by
    have i1' := i1.const_mul c₁
    have i2' := i2.const_mul c₂
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul, ← integral_add i1' i2']
    congr 1; funext p; ring
  rw [e]; ring

lemma aW_lin (B₁ B₂ : ℝ → ℂ) (c₁ c₂ : ℂ) :
    aW (fun ν => c₁ * B₁ ν + c₂ * B₂ ν) = fun ν => c₁ * aW B₁ ν + c₂ * aW B₂ ν := by
  funext ν; simp only [aW]; ring

/-- The representer of the form. -/
noncomputable def HY (B : ℝ → ℂ) : Lp ℂ 2 wNu :=
  open Classical in if hB : IsKTest B then
    Classical.choose (exists_klExt ((memLp_klInvD_muZ hB).toLp (klInvD (aW B)))) else 0

lemma HY_spec1 {B : ℝ → ℂ} (hB : IsKTest B) (f : ℝ → ℂ) (hf : IsKTest f) :
    inner ℂ ((memLp_klT_test hf).toLp (klT f)) (HY B)
      = inner ℂ ((memLp_muZ_test hf).toLp f) ((memLp_klInvD_muZ hB).toLp (klInvD (aW B))) := by
  simp only [HY, hB, dif_pos]
  exact (Classical.choose_spec (exists_klExt ((memLp_klInvD_muZ hB).toLp (klInvD (aW B))))).1 f hf

/-- **`⟨A, HY B⟩ = S(wA, wB)`.** -/
lemma HY_spec {A B : ℝ → ℂ} (hA : IsKTest A) (hB : IsKTest B) :
    inner ℂ (TL A) (HY B) = Sform (aW A) (aW B) := by
  rw [TL_of hA]
  simp only [HY, hB, dif_pos]
  rw [(Classical.choose_spec (exists_klExt ((memLp_klInvD_muZ hB).toLp (klInvD (aW B))))).2 A hA, inner_toLp_muZ, Sform]
  exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => mul_div_assoc _ _ _)

/-- `L²(w)` elements are determined by their pairing with test functions. -/
lemma eq_of_inner_test {H₁ H₂ : Lp ℂ 2 wNu} (h : ∀ A, IsKTest A → inner ℂ (TL A) H₁ = inner ℂ (TL A) H₂) :
    H₁ = H₂ := by
  have hbot := Submodule.topologicalClosure_eq_top_iff.1 testSubW_dense
  have hmem : H₁ - H₂ ∈ testSubWᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨A, hA, rfl⟩
    rw [inner_sub_right, ← TL_of hA, h A hA, sub_self]
  rw [hbot, Submodule.mem_bot] at hmem
  exact sub_eq_zero.1 hmem

lemma HY_lin {B₁ B₂ : ℝ → ℂ} (h₁ : IsKTest B₁) (h₂ : IsKTest B₂) (c₁ c₂ : ℂ) :
    HY (fun ν => c₁ * B₁ ν + c₂ * B₂ ν) = c₁ • HY B₁ + c₂ • HY B₂ := by
  refine eq_of_inner_test fun A hA => ?_
  rw [HY_spec hA (h₁.lin h₂ c₁ c₂), aW_lin, Sform_lin (isKTest_aW hA) (isKTest_aW h₁) (isKTest_aW h₂),
    inner_add_right, inner_smul_right, inner_smul_right, HY_spec hA h₁, HY_spec hA h₂]

/-! ### The bound for `HY` -/

/-- A fixed bump supported in `[1, 3]`. -/
noncomputable def phi0 (k : ℝ) : ℂ := ((max 0 (1 - |k - 2|) : ℝ) : ℂ)

lemma continuous_phi0 : Continuous phi0 := by unfold phi0; fun_prop

lemma phi0_zero_off {k : ℝ} (hk : k ∉ Icc (1 : ℝ) 3) : phi0 k = 0 := by
  have h : 1 ≤ |k - 2| := by
    by_contra hc
    push_neg at hc
    rw [abs_lt] at hc
    exact hk ⟨by linarith [hc.1], by linarith [hc.2]⟩
  simp [phi0, max_eq_left (show 1 - |k - 2| ≤ 0 by linarith)]

lemma hasCompactSupport_phi0 : HasCompactSupport phi0 :=
  HasCompactSupport.intro isCompact_Icc fun k hk => phi0_zero_off hk

lemma zero_notMem_tsupport_phi0 : (0 : ℝ) ∉ tsupport phi0 := by
  have hsub : tsupport phi0 ⊆ Icc (1 : ℝ) 3 :=
    closure_minimal (fun k hk => by
      by_contra hc
      exact hk (phi0_zero_off hc)) isClosed_Icc
  intro h
  have := hsub h
  norm_num at this

lemma phi0_two : phi0 2 = 1 := by simp [phi0]

lemma memLp_phi0 : MemLp phi0 2 (volume : Measure ℝ) := memLp_two_phi continuous_phi0 hasCompactSupport_phi0

lemma norm_toLp_phi0_pos : 0 < ‖memLp_phi0.toLp phi0‖ := by
  rw [norm_pos_iff]
  intro h0
  have h1 := memLp_phi0.coeFn_toLp
  rw [h0] at h1
  have h2 : (0 : ℝ → ℂ) =ᵐ[volume] phi0 := (Lp.coeFn_zero _ _ _).symm.trans h1
  have h3 := (Continuous.ae_eq_iff_eq (volume : Measure ℝ) continuous_zero continuous_phi0).1 h2
  have h4 := congrFun h3 2
  rw [phi0_two] at h4
  simp at h4

/-- `‖ψ ⊗ χ‖ = ‖ψ‖ ‖χ‖`. -/
lemma norm_toLp_prod {ψ χ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume : Measure ℝ)) (hχ : MemLp χ 2 wNu) :
    ‖(memLp_prod_mul hψ hχ).toLp (fun p : ℝ × ℝ => ψ p.1 * χ p.2)‖ = ‖hψ.toLp ψ‖ * ‖hχ.toLp χ‖ := by
  have h1 := norm_toLp_sq (memLp_prod_mul hψ hχ)
  have h2 := norm_toLp_sq hψ
  have h3 := norm_toLp_sq hχ
  have hψ' : AEMeasurable (fun k => ‖ψ k‖ₑ ^ (2 : ℝ)) (volume : Measure ℝ) :=
    (hψ.aestronglyMeasurable.aemeasurable.enorm).pow_const _
  have hχ' : AEMeasurable (fun ν => ‖χ ν‖ₑ ^ (2 : ℝ)) wNu :=
    (hχ.aestronglyMeasurable.aemeasurable.enorm).pow_const _
  have e : ∫⁻ p : ℝ × ℝ, ‖ψ p.1 * χ p.2‖ₑ ^ (2 : ℝ) ∂muU
      = (∫⁻ k, ‖ψ k‖ₑ ^ (2 : ℝ)) * ∫⁻ ν, ‖χ ν‖ₑ ^ (2 : ℝ) ∂wNu := by
    rw [← lintegral_prod_mul hψ' hχ']
    refine lintegral_congr fun p => ?_
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [e, ENNReal.toReal_mul, ← h2, ← h3, ← mul_pow] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

lemma norm_TL_le_eL {B : ℝ → ℂ} (hB : IsKTest B) : ‖TL B‖ ≤ ‖TL (eL 1 B)‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coe_TL hB, coe_TL (hB.eL 1)] with ν h1 h2
  rw [h1, h2, eL, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp ?_)
  have := LamK_pos ν
  positivity

/-- **`‖HY B‖ ≤ (5/2) ‖e^{Λ} B‖`** (from `fc_zero` and `Y` on products). -/
theorem norm_HY_le {B : ℝ → ℂ} (hB : IsKTest B) : ‖HY B‖ ≤ 5 / 2 * ‖TL (eL 1 B)‖ := by
  have hφc := continuous_phi0
  have hφs := hasCompactSupport_phi0
  have hφ0 := zero_notMem_tsupport_phi0
  have hB₁ := hB.eL 1
  set Ψ : L2H' := (memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₁)).toLp (PsiH phi0 (aW (eL 1 B)))
  have hΨ := klU_PsiH hφc hφs hφ0 hB₁
  set u : negLapH.domain := expDom 1 one_pos Ψ
  have hHf1 : ((klU Ψ : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] Hfun phi0 (eL 1 B) := by
    show ((klU ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₁)).toLp (PsiH phi0 (aW (eL 1 B)))) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] _
    rw [hΨ]; exact (memLp_Hfun hφc hφs hφ0 hB₁).coeFn_toLp
  have hu : ((klU (u : L2H') : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] Hfun phi0 B := by
    show ((klU ((expCut 1 one_pos).J Ψ) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] _
    filter_upwards [klU_expCut one_pos Ψ, hHf1] with p h1 h2
    rw [h1, h2]
    simp only [Hfun, eL]
    have he : ((Real.exp (-(1 * LamK p.2)) : ℝ) : ℂ) * ((Real.exp (1 * LamK p.2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    linear_combination (phi0 p.1 * B p.2) * he
  have hG := klU_domY_Hfun hφc hφs hB u hu (HY B) (HY_spec1 hB)
  have hχ : MemLp (fun ν => (1 / 2 : ℂ) * B ν + HY B ν) 2 wNu := ((memLp_wNu hB).const_mul (1 / 2)).add (Lp.memLp _)
  have m₀ := memLp_prod_mul memLp_phi0 hχ
  have hEq : klU (domY u) = m₀.toLp _ := Lp.ext (hG.trans m₀.coeFn_toLp.symm)
  have hY := (fc_zero one_pos Ψ).2.2
  have hn1 : ‖memLp_phi0.toLp phi0‖ * ‖hχ.toLp _‖ ≤ 2 / 1 * ‖Ψ‖ := by
    rw [← norm_toLp_prod memLp_phi0 hχ, ← hEq, norm_klU]; exact hY
  have hn2 : ‖Ψ‖ = ‖memLp_phi0.toLp phi0‖ * ‖TL (eL 1 B)‖ := by
    have h2 := norm_toLp_prod memLp_phi0 (memLp_wNu hB₁)
    rw [TL_of hB₁, ← h2, ← norm_klU Ψ]
    show ‖klU ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hB₁)).toLp (PsiH phi0 (aW (eL 1 B))))‖ = _
    rw [hΨ]; rfl
  have hpos := norm_toLp_phi0_pos
  have hn3 : ‖hχ.toLp (fun ν => (1 / 2 : ℂ) * B ν + HY B ν)‖ ≤ 2 * ‖TL (eL 1 B)‖ := by
    rw [hn2] at hn1
    have := le_of_mul_le_mul_left (a := ‖memLp_phi0.toLp phi0‖)
      (by calc ‖memLp_phi0.toLp phi0‖ * ‖hχ.toLp (fun ν => (1 / 2 : ℂ) * B ν + HY B ν)‖
              ≤ 2 / 1 * (‖memLp_phi0.toLp phi0‖ * ‖TL (eL 1 B)‖) := hn1
            _ = ‖memLp_phi0.toLp phi0‖ * (2 * ‖TL (eL 1 B)‖) := by ring) hpos
    exact this
  have hsum : hχ.toLp (fun ν => (1 / 2 : ℂ) * B ν + HY B ν) = (1 / 2 : ℂ) • TL B + HY B := by
    apply Lp.ext
    filter_upwards [hχ.coeFn_toLp, Lp.coeFn_add ((1 / 2 : ℂ) • TL B) (HY B), Lp.coeFn_smul (1 / 2 : ℂ) (TL B), coe_TL hB]
      with ν e1 e2 e3 e4
    rw [e1, e2]
    simp only [Pi.add_apply]
    rw [e3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e4]
  rw [hsum] at hn3
  have hT : ‖(1 / 2 : ℂ) • TL B‖ = 1 / 2 * ‖TL B‖ := by
    rw [norm_smul]; norm_num
  have htri : ‖HY B‖ ≤ ‖(1 / 2 : ℂ) • TL B + HY B‖ + ‖(1 / 2 : ℂ) • TL B‖ := by
    have := norm_sub_le ((1 / 2 : ℂ) • TL B + HY B) ((1 / 2 : ℂ) • TL B)
    rwa [add_sub_cancel_left] at this
  have hle := norm_TL_le_eL hB
  rw [hT] at htri
  linarith

/-! ### Differentiating along exponential curves -/

/-- **The derivative of `s ↦ L(e^{σ s Λ}C)`** for a linear `L` bounded by `κ ‖e^{Λ}·‖`. -/
theorem curve_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {L : (ℝ → ℂ) → E} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlin : ∀ {B₁ B₂ : ℝ → ℂ}, IsKTest B₁ → IsKTest B₂ → ∀ c₁ c₂ : ℂ,
      L (fun ν => c₁ * B₁ ν + c₂ * B₂ ν) = c₁ • L B₁ + c₂ • L B₂)
    (hbd : ∀ {B : ℝ → ℂ}, IsKTest B → ‖L B‖ ≤ κ * ‖TL (eL 1 B)‖)
    (σ : ℝ) {C : ℝ → ℂ} (hC : IsKTest C) (s : ℝ) :
    HasDerivAt (fun s => L (eL (σ * s) C)) (σ • L (mL (eL (σ * s) C))) s := by
  obtain ⟨M, hM⟩ := hC.compact.exists_bound_of_continuousOn continuous_LamK.continuousOn
  have hM0 : ∀ ν, C ν ≠ 0 → LamK ν ≤ M := fun ν hν =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM ν (subset_tsupport _ hν)))
  set h₀ : ℝ := 1 / (|σ| * |M| + 1)
  have hh₀ : 0 < h₀ := by positivity
  set Ĝ : ℝ → ℂ := mL (mL (eL (σ * s + 1) C))
  have hĜ : IsKTest Ĝ := (hC.eL _).mL.mL
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_ (isLittleO_pow_id (by norm_num))
  refine IsBigO.of_bound (κ * (σ ^ 2 * ‖TL Ĝ‖)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hh₀] with h hh
  have habs : |h| < h₀ := by simpa [Real.dist_eq] using hh
  have hP₁ := hC.eL (σ * (s + h))
  have hP₂ := hC.eL (σ * s)
  have hP₃ := hP₂.mL
  -- the combination
  set Δ : ℝ → ℂ := fun ν => (1 : ℂ) * eL (σ * (s + h)) C ν
    + (-1 : ℂ) * ((1 : ℂ) * eL (σ * s) C ν + ((h * σ : ℝ) : ℂ) * mL (eL (σ * s) C) ν)
  have hΔ : IsKTest Δ := hP₁.lin (hP₂.lin hP₃ 1 _) 1 (-1)
  have eΔ : L Δ = L (eL (σ * (s + h)) C) - L (eL (σ * s) C) - h • σ • L (mL (eL (σ * s) C)) := by
    simp only [Δ]
    rw [hlin hP₁ (hP₂.lin hP₃ 1 _), hlin hP₂ hP₃, one_smul, one_smul, smul_add, neg_one_smul, neg_one_smul,
      show ((h * σ : ℝ) : ℂ) • L (mL (eL (σ * s) C)) = h • σ • L (mL (eL (σ * s) C)) by
        rw [smul_smul]; exact algebraMap_smul ℂ (h * σ) _]
    abel
  rw [← eΔ]
  have hbΔ := hbd hΔ
  -- the pointwise Taylor bound
  have hpt : ‖TL (eL 1 Δ)‖ ≤ (σ ^ 2 * |h| ^ 2) * ‖TL Ĝ‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coe_TL (hΔ.eL 1), coe_TL hĜ] with ν h1 h2
    rw [h1, h2]
    by_cases hc : C ν = 0
    · simp [eL, Δ, mL, Ĝ, hc]
    · set x := LamK ν
      have hx0 : 0 < x := LamK_pos ν
      have hxM : x ≤ M := hM0 ν hc
      have hδ : |σ * h * x| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_of_pos hx0]
        have hM' : x ≤ |M| := hxM.trans (le_abs_self _)
        have h1 : |h| * (|σ| * |M| + 1) ≤ 1 := by
          have := mul_le_mul_of_nonneg_right habs.le (by positivity : 0 ≤ |σ| * |M| + 1)
          simp only [h₀] at this
          rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
        have h2 : |σ| * x ≤ |σ| * |M| := by gcongr
        nlinarith [abs_nonneg h, abs_nonneg σ]
      have hT := Real.abs_exp_sub_one_sub_id_le hδ
      have hE := Real.exp_pos (σ * s * x)
      have hE1 := Real.exp_pos x
      have eD : eL 1 Δ ν = ((Real.exp (1 * x) * Real.exp (σ * s * x) * (Real.exp (σ * h * x) - 1 - σ * h * x) : ℝ) : ℂ) * C ν := by
        simp only [eL, Δ, mL]
        have e1 : Real.exp (σ * (s + h) * LamK ν) = Real.exp (σ * s * x) * Real.exp (σ * h * x) := by
          rw [← Real.exp_add]; congr 1; simp only [x]; ring
        rw [e1]; simp only [x]; push_cast; ring
      have eG : Ĝ ν = ((x * x * Real.exp ((σ * s + 1) * x) : ℝ) : ℂ) * C ν := by
        simp only [Ĝ, eL, mL, x]; push_cast; ring
      rw [eD, eG, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hE,
        abs_of_pos (by positivity : 0 < x * x * Real.exp ((σ * s + 1) * x))]
      have e3 : Real.exp ((σ * s + 1) * x) = Real.exp (1 * x) * Real.exp (σ * s * x) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e3, ← mul_assoc, ← mul_assoc]
      have hkey : Real.exp (1 * x) * Real.exp (σ * s * x) * |Real.exp (σ * h * x) - 1 - σ * h * x|
          ≤ σ ^ 2 * |h| ^ 2 * (x * x * (Real.exp (1 * x) * Real.exp (σ * s * x))) := by
        have hb : |Real.exp (σ * h * x) - 1 - σ * h * x| ≤ σ ^ 2 * |h| ^ 2 * (x * x) := by
          refine hT.trans (le_of_eq ?_)
          rw [sq_abs]; ring
        calc _ ≤ Real.exp (1 * x) * Real.exp (σ * s * x) * (σ ^ 2 * |h| ^ 2 * (x * x)) := by gcongr
          _ = _ := by ring
      calc _ ≤ σ ^ 2 * |h| ^ 2 * (x * x * (Real.exp (1 * x) * Real.exp (σ * s * x))) * ‖C ν‖ := by gcongr
        _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  calc ‖L Δ‖ ≤ κ * ‖TL (eL 1 Δ)‖ := hbΔ
    _ ≤ κ * ((σ ^ 2 * |h| ^ 2) * ‖TL Ĝ‖) := by gcongr
    _ = κ * (σ ^ 2 * ‖TL Ĝ‖) * h ^ 2 := by rw [sq_abs]; ring

end Qschubert
