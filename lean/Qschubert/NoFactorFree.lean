import Qschubert.Nonvac

/-!
# No factor-free pointwise bound on the modular surface (`cl:main`, "Consequently", from (ii))

`Stmt_cl_noFactorFree`: for the printed-class amplitude `a = e^{-αΛ}e^{-κX₀}` of `cl:main` (ii) (with
`β = 1`, `κ = max(κ*, 2)`, `α = min(α₀, c₁κ^{-6})`), for every `p ≥ 0` and all `C, δ, ħ₁ > 0` there are
`0 < ħ ≤ ħ₁`, `0 ≤ t ≤ δ (α/ħ)^{1/2}` and `x` at which the error exceeds `C (αħ)^{-p} ‖a‖` (every
continuous representative, which exists). Proof from `cl:main` (ii) at `t = (2p+4) log(1/ħ)`.
-/

namespace Qschubert

open Real Filter MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups

/-- The algebra at `ħ = 1/u`, `t = (2p+4) log u`. -/
lemma refute_key_p {u c C N α p : ℝ} (hu : 1 ≤ u) (hc : 0 < c) (hα : 0 < α) (hp : 0 ≤ p)
    (h : C * α ^ (-p) * N / ((2 * p + 4) * c) < u ^ ((1 : ℝ) / 2) * log u) :
    C * (α * (1 / u)) ^ (-p) * N
      < c * exp ((2 * p + 4) * log u / 2) * (1 / u) ^ ((3 : ℝ) / 2) * ((2 * p + 4) * log u) := by
  have hu0 : 0 < u := by linarith
  have e1 : (α * (1 / u)) ^ (-p) = α ^ (-p) * u ^ p := by
    rw [Real.mul_rpow hα.le (by positivity), one_div, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le,
      neg_neg]
  have e2 : exp ((2 * p + 4) * log u / 2) = u ^ (p + 2) := by
    rw [Real.rpow_def_of_pos hu0]; congr 1; ring
  have e3 : (1 / u) ^ ((3 : ℝ) / 2) = (u ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow hu0.le]
  have e4 : u ^ (p + 2) = u ^ p * u ^ ((1 : ℝ) / 2) * u ^ ((3 : ℝ) / 2) := by
    rw [mul_assoc, ← Real.rpow_add hu0, ← Real.rpow_add hu0]; norm_num
  have hp32 : 0 < u ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hu0 _
  have hup : 0 < u ^ p := Real.rpow_pos_of_pos hu0 _
  have hk : 0 < (2 * p + 4) * c := by positivity
  rw [e1, e2, e3, e4]
  have h' := (div_lt_iff₀ hk).1 h
  calc C * (α ^ (-p) * u ^ p) * N = u ^ p * (C * α ^ (-p) * N) := by ring
    _ < u ^ p * (u ^ ((1 : ℝ) / 2) * log u * ((2 * p + 4) * c)) := by gcongr
    _ = c * (u ^ p * u ^ ((1 : ℝ) / 2) * u ^ ((3 : ℝ) / 2)) * (u ^ ((3 : ℝ) / 2))⁻¹
          * ((2 * p + 4) * log u) := by
        field_simp

/-- **No factor-free bound** (`cl:main`, "Consequently", printed class): there are `α > 0`, `κ > 1`
(the amplitude `a = e^{-αΛ}e^{-κX₀}`, finite printed norm with `β = 1`) such that for every `p ≥ 0`
and all `C`, `δ > 0`, `ħ₁ > 0` the error at some `x + i e^t`, `0 < ħ ≤ ħ₁`, `0 ≤ t ≤ δ (α/ħ)^{1/2}`,
exceeds `C (αħ)^{-p} ‖a‖` for its continuous representative (which exists). -/
def Stmt_cl_noFactorFree : Prop :=
  ∃ (α κ : ℝ) (hα : 0 < α), 1 < κ ∧ prNormX I α 1 (ampCl2 α κ hα.le) < ⊤ ∧
  ∀ p C δ ħ₁ : ℝ, 0 ≤ p → 0 < δ → 0 < ħ₁ →
  ∃ ħ' t x : ℝ, 0 < ħ' ∧ ħ' ≤ ħ₁ ∧ 0 ≤ t ∧ t ≤ δ * Real.sqrt (α / ħ') ∧
    ∃ (hv : PerioConv modGroup (initState 1 ħ' (ampCl2 α κ hα.le)))
      (hw : PerioConv modGroup (approxSolB 1 0 ħ' t (ampCl2 α κ hα.le))),
      (∃ f : Surf modGroup → ℂ, Continuous f ∧ f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw)) ∧
      ∀ f : Surf modGroup → ℂ, Continuous f → f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw) →
        C * (α * ħ') ^ (-p) * (prNormX I α 1 (ampCl2 α κ hα.le)).toReal
          < ‖f (surfMk modGroup (ptXT x t))‖

/-- **`cl:main` (ii) implies the no-factor-free-bound clause.** -/
theorem cl_noFactorFree_of_clmain2 (h2 : Stmt_clmain2) : Stmt_cl_noFactorFree := by
  unfold Stmt_clmain2 at h2
  obtain ⟨α₀max, κs, c₁, hα₀, -, hκs, hc₁, h2'⟩ := h2
  set κ : ℝ := max κs 2 with hκdef
  have hκ1 : 1 < κ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hκpos : 0 < κ := by linarith
  set α : ℝ := min α₀max (c₁ * κ ^ (-(6 : ℤ))) with hαdef
  have hα : 0 < α := lt_min hα₀ (mul_pos hc₁ (zpow_pos hκpos _))
  have hfin := supp_prNormCl2 α κ hα.le hκ1
  refine ⟨α, κ, hα, hκ1, hfin, ?_⟩
  intro p C δ ħ₁ hp hδ hħ₁
  obtain ⟨ħ₀, c, t₀, δ', hħ₀, hc, ht₀, hδ', hcl⟩ := h2' κ α (le_max_left _ _) hα le_rfl
  set N := (prNormX I α 1 (ampCl2 α κ hα.le)).toReal with hNdef
  have hinv : Tendsto (fun u : ℝ => 1 / u) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero
  have ev : ∀ᶠ u in atTop, 1 ≤ u ∧ 1 / u ≤ ħ₀ ∧ 1 / u ≤ ħ₁ ∧ t₀ ≤ (2 * p + 4) * log u
      ∧ (2 * p + 4) * log u ≤ 1 * u ^ ((1 : ℝ) / 5)
      ∧ (2 * p + 4) * log u ≤ (δ' * √α) * u ^ ((1 : ℝ) / 2)
      ∧ (2 * p + 4) * log u ≤ (δ * √α) * u ^ ((1 : ℝ) / 2)
      ∧ C * α ^ (-p) * N / ((2 * p + 4) * c) < u ^ ((1 : ℝ) / 2) * log u := by
    refine (eventually_ge_atTop 1).and ((hinv.eventually (ge_mem_nhds hħ₀)).and
      ((hinv.eventually (ge_mem_nhds hħ₁)).and
      (((tendsto_log_atTop.const_mul_atTop (by linarith : (0 : ℝ) < 2 * p + 4)).eventually_ge_atTop t₀).and
      ((eventually_log_le_rpow one_pos (by norm_num)).and
      ((eventually_log_le_rpow (by positivity) (by norm_num)).and
      ((eventually_log_le_rpow (by positivity) (by norm_num)).and
      (eventually_lt_sqrt_mul_log _)))))))
  obtain ⟨u, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8⟩ := ev.exists
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ log u := log_nonneg hu1
  set ħ' : ℝ := 1 / u with hħdef
  set t : ℝ := (2 * p + 4) * log u with htdef
  have hħpos : 0 < ħ' := by positivity
  have hlogħ : log (1 / ħ') = log u := by rw [hħdef, one_div_one_div]
  have hsq : √(α / ħ') = √α * u ^ ((1 : ℝ) / 2) := by
    rw [hħdef, show α / (1 / u) = α * u by field_simp, Real.sqrt_mul hα.le, Real.sqrt_eq_rpow u]
  have hpow : ħ' ^ (-(1 : ℝ) / 5) = u ^ ((1 : ℝ) / 5) := by
    rw [hħdef, one_div, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]
    congr 1; ring
  have hwin : ClWindow ħ' t t₀ δ' α := by
    refine ⟨max_le ?_ hu4, le_min ?_ ?_⟩
    · rw [hlogħ]; nlinarith
    · rw [hpow]; linarith
    · rw [hsq]; linarith
  obtain ⟨hv, hw, ⟨hex, hall⟩, -⟩ := hcl ħ' t 0 hħpos hu2 hwin
  refine ⟨ħ', t, 0, hħpos, hu3, by positivity, by rw [hsq]; linarith, hv, hw, hex, fun f hfc hfae => ?_⟩
  have hlow := hall f hfc hfae
  have key := refute_key_p hu1 hc hα hp hu8
  rw [← hħdef, ← htdef] at key
  linarith

/-- `m(z) ≥ 1`: the identity is in the counting set. -/
lemma one_le_orbitMult (Γ : Subgroup PGL(2, ℝ)) (z : ℍ) : 1 ≤ orbitMult Γ z := by
  unfold orbitMult
  rw [Set.one_le_encard_iff_nonempty]
  exact ⟨1, by simp⟩

/-- The algebra at `ħ = v^{-5}`, `t = v`. -/
lemma mult_key {v c Cp N g p : ℝ} (hv : 1 ≤ v) (hc : 0 < c) (_hCp : 0 ≤ Cp) (_hN : 0 ≤ N)
    (h : Cp * 5 ^ g * N / c < exp ((1 / 2 - g) * v) / v ^ (5 * p + 13 / 2)) :
    Cp * (5 * exp v) ^ g * ((v ^ (5 : ℕ))⁻¹) ^ (-p) * N
      < c * exp (v / 2) * ((v ^ (5 : ℕ))⁻¹) ^ ((3 : ℝ) / 2) * v := by
  have hv0 : 0 < v := by linarith
  have hv5 : (v ^ (5 : ℕ) : ℝ) = v ^ (5 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have e1 : ((v ^ (5 : ℕ))⁻¹) ^ (-p) = v ^ (5 * p) := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv, hv5,
      ← Real.rpow_mul hv0.le]
  have e2 : ((v ^ (5 : ℕ))⁻¹) ^ ((3 : ℝ) / 2) * v = (v ^ ((13 : ℝ) / 2))⁻¹ := by
    rw [Real.inv_rpow (by positivity), hv5, ← Real.rpow_mul hv0.le]
    have : v ^ ((5 : ℝ) * (3 / 2)) = v ^ ((13 : ℝ) / 2) * v := by
      rw [show (5 : ℝ) * (3 / 2) = 13 / 2 + 1 by norm_num, Real.rpow_add hv0, Real.rpow_one]
    rw [this]; field_simp
  have e3 : (5 * exp v) ^ g = 5 ^ g * exp (g * v) := by
    rw [Real.mul_rpow (by norm_num) (exp_pos v).le, ← Real.exp_mul, mul_comm v g]
  have e4 : exp (v / 2) = exp ((1 / 2 - g) * v) * exp (g * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have e5 : v ^ (5 * p + 13 / 2) = v ^ (5 * p) * v ^ ((13 : ℝ) / 2) := Real.rpow_add hv0 _ _
  have hA : 0 < v ^ (5 * p) := Real.rpow_pos_of_pos hv0 _
  have hB : 0 < v ^ ((13 : ℝ) / 2) := Real.rpow_pos_of_pos hv0 _
  have hE : 0 < exp (g * v) := exp_pos _
  rw [e5, div_lt_div_iff₀ hc (by positivity)] at h
  have hR : c * exp (v / 2) * ((v ^ (5 : ℕ))⁻¹) ^ ((3 : ℝ) / 2) * v
      = c * (exp ((1 / 2 - g) * v) * exp (g * v)) * (v ^ ((13 : ℝ) / 2))⁻¹ := by
    rw [mul_assoc (c * exp (v / 2)), e2, e4]
  rw [e1, e3, hR, ← div_eq_mul_inv, lt_div_iff₀ hB]
  have := mul_lt_mul_of_pos_right h hE
  calc Cp * (5 ^ g * exp (g * v)) * v ^ (5 * p) * N * v ^ ((13 : ℝ) / 2)
      = Cp * 5 ^ g * N * (v ^ (5 * p) * v ^ ((13 : ℝ) / 2)) * exp (g * v) := by ring
    _ < exp ((1 / 2 - g) * v) * c * exp (g * v) := this
    _ = c * (exp ((1 / 2 - g) * v) * exp (g * v)) := by ring

/-- **No bound `C m(z)^γ ħ^{-p} ‖a‖` with `γ < 1/2`** (`cl:main`, "Consequently", printed class): for
the amplitude `a = e^{-αΛ}e^{-κX₀}` of `cl:main` (ii), for every `γ < 1/2`, `p ≥ 0` and all `C`,
`δ > 0`, `ħ₁ > 0` the error at some `x + i e^t`, `0 < ħ ≤ ħ₁`, `0 ≤ t ≤ δ(α/ħ)^{1/2}`, exceeds
`C m(z)^γ ħ^{-p} ‖a‖` (`m(z)` finite) for its continuous representative (which exists). -/
def Stmt_cl_noMultFactor : Prop :=
  ∃ (α κ : ℝ) (hα : 0 < α), 1 < κ ∧ prNormX I α 1 (ampCl2 α κ hα.le) < ⊤ ∧
  ∀ γ p C δ ħ₁ : ℝ, γ < 1 / 2 → 0 ≤ p → 0 < δ → 0 < ħ₁ →
  ∃ ħ' t x : ℝ, 0 < ħ' ∧ ħ' ≤ ħ₁ ∧ 0 ≤ t ∧ t ≤ δ * Real.sqrt (α / ħ') ∧
    ∃ (hv : PerioConv modGroup (initState 1 ħ' (ampCl2 α κ hα.le)))
      (hw : PerioConv modGroup (approxSolB 1 0 ħ' t (ampCl2 α κ hα.le))),
      (∃ f : Surf modGroup → ℂ, Continuous f ∧ f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw)) ∧
      (multM modGroup (surfMk modGroup (ptXT x t)) : ℝ≥0∞) < ⊤ ∧
      ∀ f : Surf modGroup → ℂ, Continuous f → f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw) →
        C * ((multM modGroup (surfMk modGroup (ptXT x t)) : ℝ≥0∞).toReal) ^ γ * ħ' ^ (-p)
          * (prNormX I α 1 (ampCl2 α κ hα.le)).toReal < ‖f (surfMk modGroup (ptXT x t))‖

/-- **`cl:main` (ii) implies the `m(z)^γ` clause.** -/
theorem cl_noMultFactor_of_clmain2 (h2 : Stmt_clmain2) : Stmt_cl_noMultFactor := by
  unfold Stmt_clmain2 at h2
  obtain ⟨α₀max, κs, c₁, hα₀, -, hκs, hc₁, h2'⟩ := h2
  set κ : ℝ := max κs 2 with hκdef
  have hκ1 : 1 < κ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hκpos : 0 < κ := by linarith
  set α : ℝ := min α₀max (c₁ * κ ^ (-(6 : ℤ))) with hαdef
  have hα : 0 < α := lt_min hα₀ (mul_pos hc₁ (zpow_pos hκpos _))
  have hfin := supp_prNormCl2 α κ hα.le hκ1
  refine ⟨α, κ, hα, hκ1, hfin, ?_⟩
  intro γ p C δ ħ₁ hγ hp hδ hħ₁
  obtain ⟨ħ₀, c, t₀, δ', hħ₀, hc, ht₀, hδ', hcl⟩ := h2' κ α (le_max_left _ _) hα le_rfl
  set N := (prNormX I α 1 (ampCl2 α κ hα.le)).toReal with hNdef
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set g := max γ 0 with hgdef
  have hg0 : 0 ≤ g := le_max_right _ _
  have hg : g < 1 / 2 := max_lt hγ (by norm_num)
  set Cp := max C 0 with hCpdef
  have hCp : 0 ≤ Cp := le_max_right _ _
  have hinv : Tendsto (fun v : ℝ => (v ^ (5 : ℕ))⁻¹) atTop (nhds 0) :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).inv_tendsto_atTop
  have hgrow : ∀ K' : ℝ, 0 < K' → ∀ᶠ v in atTop, v ≤ K' * v ^ ((5 : ℝ) / 2) := by
    intro K' hK'
    filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 3 / 2 by norm_num)).eventually_ge_atTop (1 / K'),
      eventually_ge_atTop (1 : ℝ)] with v hv hv1
    have hv0 : 0 < v := by linarith
    rw [show (5 : ℝ) / 2 = 1 + 3 / 2 by norm_num, Real.rpow_add hv0, Real.rpow_one]
    have : 1 ≤ K' * v ^ ((3 : ℝ) / 2) := by
      rw [div_le_iff₀ hK'] at hv; linarith
    nlinarith
  have ev : ∀ᶠ v in atTop, 1 ≤ v ∧ (v ^ (5 : ℕ))⁻¹ ≤ ħ₀ ∧ (v ^ (5 : ℕ))⁻¹ ≤ ħ₁ ∧ t₀ ≤ v
      ∧ 10 * log v ≤ 1 * v ^ (1 : ℝ)
      ∧ v ≤ (δ' * √α) * v ^ ((5 : ℝ) / 2) ∧ v ≤ (δ * √α) * v ^ ((5 : ℝ) / 2)
      ∧ Cp * 5 ^ g * N / c < exp ((1 / 2 - g) * v) / v ^ (5 * p + 13 / 2) := by
    refine (eventually_ge_atTop 1).and ((hinv.eventually (ge_mem_nhds hħ₀)).and
      ((hinv.eventually (ge_mem_nhds hħ₁)).and ((eventually_ge_atTop t₀).and
      ((eventually_log_le_rpow one_pos one_pos).and ((hgrow _ (by positivity)).and
      ((hgrow _ (by positivity)).and
      ((tendsto_exp_mul_div_rpow_atTop _ _ (by linarith)).eventually_gt_atTop _)))))))
  obtain ⟨v, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩ := ev.exists
  have hv0 : 0 < v := by linarith
  set ħ' : ℝ := (v ^ (5 : ℕ))⁻¹ with hħdef
  have hħpos : 0 < ħ' := by positivity
  have hv5r : (v ^ (5 : ℕ) : ℝ) = v ^ (5 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hlogħ : log (1 / ħ') = 5 * log v := by
    rw [hħdef, one_div, inv_inv, Real.log_pow]; norm_num
  have hsq : √(α / ħ') = √α * v ^ ((5 : ℝ) / 2) := by
    rw [hħdef, div_inv_eq_mul, Real.sqrt_mul hα.le, Real.sqrt_eq_rpow (v ^ (5 : ℕ)), hv5r,
      ← Real.rpow_mul hv0.le]
    norm_num
  have hpow : ħ' ^ (-(1 : ℝ) / 5) = v := by
    rw [hħdef, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), hv5r,
      ← Real.rpow_mul hv0.le]
    norm_num
  have hwin : ClWindow ħ' v t₀ δ' α := by
    refine ⟨max_le ?_ hv4, le_min ?_ ?_⟩
    · rw [hlogħ]; rw [Real.rpow_one] at hv5; linarith
    · rw [hpow]
    · rw [hsq]; linarith
  obtain ⟨hv, hw, ⟨hex, hall⟩, hm⟩ := hcl ħ' v 0 hħpos hv2 hwin
  have hmtop : (multM modGroup (surfMk modGroup (ptXT 0 v)) : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  refine ⟨ħ', v, 0, hħpos, hv3, hv0.le, by rw [hsq]; linarith, hv, hw, hex, hmtop, fun f hfc hfae => ?_⟩
  have hlow := hall f hfc hfae
  set M := ((multM modGroup (surfMk modGroup (ptXT 0 v)) : ℝ≥0∞)).toReal with hMdef
  have hM5 : M ≤ 5 * exp v := ENNReal.toReal_le_of_le_ofReal (by positivity) hm
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ≥0∞) ≤ (multM modGroup (surfMk modGroup (ptXT 0 v)) : ℝ≥0∞) := by
      rw [multM_mk]; exact_mod_cast one_le_orbitMult modGroup _
    have := ENNReal.toReal_mono hmtop.ne h1
    simpa using this
  have hMg : M ^ γ ≤ (5 * exp v) ^ g := by
    rcases le_or_gt 0 γ with hγ0 | hγ0
    · rw [show g = γ from max_eq_left hγ0]
      exact Real.rpow_le_rpow (by linarith) hM5 hγ0
    · rw [show g = 0 from max_eq_right hγ0.le, Real.rpow_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos hM1 hγ0.le
  have hMpos : 0 ≤ M ^ γ := Real.rpow_nonneg (by linarith) _
  have hħp : 0 ≤ ħ' ^ (-p) := Real.rpow_nonneg hħpos.le _
  have key := mult_key hv1 hc hCp hN0 hv8
  rw [← hħdef] at key
  calc C * M ^ γ * ħ' ^ (-p) * N ≤ Cp * M ^ γ * ħ' ^ (-p) * N := by
        have : C ≤ Cp := le_max_left _ _
        have h0 : 0 ≤ M ^ γ * ħ' ^ (-p) * N := by positivity
        nlinarith
    _ ≤ Cp * (5 * exp v) ^ g * ħ' ^ (-p) * N := by gcongr
    _ < c * exp (v / 2) * ħ' ^ ((3 : ℝ) / 2) * v := key
    _ ≤ ‖f (surfMk modGroup (ptXT 0 v))‖ := hlow

end Qschubert
