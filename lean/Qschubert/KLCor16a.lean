import Qschubert.KLDDThm

/-!
# Local regularity on `M`, for Corollary 1.6R

For `u ∈ Dom(-Δ_M)` and a real test function `χ` on `ℍ` whose support meets each `Γ`-orbit at most once, `χ ũ ∈ L²(ℍ)`, where `ũ` is the lift of `u` (`cutV`). The lift solves the
equation weakly on `ℍ` (`cut_pair`, `weak_tests`). A first step puts `χ ũ` in the form space (`form_step`, by Riesz), and a second one puts `χ₂ ũ` in `Dom(-Δ)` on `ℍ`, for a smaller cutoff.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `(1 - Δ)` on test functions has dense range. -/
lemma eq_zero_of_perp {y : L2H'} (h : ∀ P : testFn, ⟪y, toL2 P - toL2 (lapTest P)⟫_ℂ = 0) : y = 0 := by
  have hw : ∀ G : testFn, ⟪toL2 (lapTest G), y⟫_ℂ = ⟪toL2 G, y⟫_ℂ := fun G => by
    have h1 := h G
    rw [inner_sub_right, sub_eq_zero] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [inner_conj_symm] at h2
    exact h2.symm
  obtain ⟨hv, hn⟩ := mem_negLapH_of_weak hw
  have he := energy_dom ⟨y, hv⟩
  rw [hn, inner_neg_right, Complex.neg_re, inner_self_eq_norm_sq_to_K] at he
  have h3 : (((‖y‖ : ℝ) : ℂ) ^ 2).re = ‖y‖ ^ 2 := by
    norm_cast
  have h3' : ((((‖y‖ : ℝ) : ℂ) ^ 2 : ℂ)).re = ‖y‖ ^ 2 := h3
  have h4 : ‖y‖ ^ 2 ≤ 0 := by
    have hX := sq_nonneg ‖domX ⟨y, hv⟩‖
    have hY := sq_nonneg ‖domY ⟨y, hv⟩‖
    simp only [Complex.coe_algebraMap] at he
    rw [h3'] at he
    linarith
  have h5 : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.1 h5

/-- **Riesz on the form space.** A functional `P ↦ ⟪v, (1 - Δ)P⟫` bounded in the form norm puts `v` in the form space. -/
theorem exists_form_of_bound {v : L2H'} {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ P : testFn, ‖⟪v, toL2 P - toL2 (lapTest P)⟫_ℂ‖ ≤ B * Real.sqrt (‖toL2 P‖ ^ 2 + ‖toL2 (vfTest 1 P)‖ ^ 2 + ‖toL2 (vfTest Complex.I P)‖ ^ 2)) :
    ∃ ξ : FormSpace negLap, formIncl negLap ξ = v ∧ ‖ξ‖ ≤ B := by
  let L : FormDom negLap →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪v, FormDom.val negLap x + FormDom.app negLap x⟫_ℂ
      map_add' := fun x y => by
        rw [FormDom.val_add, FormDom.app_add, add_add_add_comm, inner_add_right]
      map_smul' := fun c x => by
        rw [FormDom.val_smul, FormDom.app_smul, ← smul_add, inner_smul_right]
        rfl }
  have hLv : ∀ x : FormDom negLap, L x = ⟪v, toL2 (toL2Equiv.symm (FormDom.toDom negLap x)) - toL2 (lapTest (toL2Equiv.symm (FormDom.toDom negLap x)))⟫_ℂ := fun x => by
    show ⟪v, FormDom.val negLap x + FormDom.app negLap x⟫_ℂ = _
    rw [formDom_val_eq, formDom_app_eq, sub_eq_add_neg]
  have hLb : ∀ x : FormDom negLap, ‖L x‖ ≤ B * ‖x‖ := fun x => by
    rw [hLv]
    refine (h _).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hB0)
    rw [← form_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  let Lc : FormDom negLap →L[ℂ] ℂ := L.mkContinuous B hLb
  let Λ : FormSpace negLap →L[ℂ] ℂ := Lc.extend (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap)
  have hΛc : ∀ x : FormDom negLap, Λ (x : FormSpace negLap) = L x := fun x =>
    ContinuousLinearMap.extend_eq Lc (e := (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap))
      UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) x
  have hΛb : ‖Λ‖ ≤ B := by
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun q => ?_
    refine UniformSpace.Completion.induction_on q ?_ ?_
    · exact isClosed_le Λ.continuous.norm (continuous_const.mul continuous_norm)
    · intro x
      rw [hΛc, UniformSpace.Completion.norm_coe]
      exact hLb x
  set ξ : FormSpace negLap := (InnerProductSpace.toDual ℂ (FormSpace negLap)).symm Λ with hξ
  have hξin : ∀ y, ⟪ξ, y⟫_ℂ = Λ y := fun y => InnerProductSpace.toDual_symm_apply
  refine ⟨ξ, ?_, ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_perp fun P => ?_)
    set x : FormDom negLap := FormDom.ofDom negLap (toL2Equiv P) with hx
    have e0 : toL2Equiv.symm (FormDom.toDom negLap x) = P := by
      show toL2Equiv.symm (toL2Equiv P) = P
      exact toL2Equiv.symm_apply_apply P
    have e1 : FormDom.val negLap x + FormDom.app negLap x = toL2 P - toL2 (lapTest P) := by
      rw [formDom_val_eq, formDom_app_eq, e0, sub_eq_add_neg]
    have h1 := inner_coe_formSpace negLap x ξ
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [inner_conj_symm] at h2
    rw [hξin, hΛc] at h2
    rw [inner_sub_left, ← e1, ← h2]
    show L x - L x = 0
    exact sub_self _
  · rw [hξ, LinearIsometryEquiv.norm_map]
    exact hΛb

section cut

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)

/-- The lift of `u` to `ℍ`. -/
noncomputable def liftM (u : L2M) : ℍ → ℂ := fun z => (u : Surf Γ → ℂ) (surfMk Γ z)

lemma measurable_liftM (u : L2M) : Measurable (liftM Γ u) :=
  (Lp.stronglyMeasurable u).measurable.comp (measurable_surfMk Γ)

lemma liftM_smul (u : L2M) (γ : Γ) (z : ℍ) : liftM Γ u (γ • z) = liftM Γ u z := by
  simp only [liftM, surfMk_smul]

/-- The support of `χ` meets every orbit at most once. -/
def InjT (χ : testFn) : Prop := ∀ (z : ℍ) (γ : Γ), γ ≠ 1 → (χ : ℂ → ℂ) z ≠ 0 → (χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ) = 0

lemma exists_supT (χ : testFn) : ∃ S : ℝ, 0 ≤ S ∧ ∀ w, ‖(χ : ℂ → ℂ) w‖ ≤ S := by
  obtain ⟨C, hC⟩ := χ.2.smooth.continuous.bounded_above_of_compact_support χ.2.compact
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩

/-- A bound of `χ`. -/
noncomputable def supT (χ : testFn) : ℝ := Classical.choose (exists_supT χ)

lemma supT_nonneg (χ : testFn) : 0 ≤ supT χ := (Classical.choose_spec (exists_supT χ)).1

lemma norm_le_supT (χ : testFn) (w : ℂ) : ‖(χ : ℂ → ℂ) w‖ ≤ supT χ := (Classical.choose_spec (exists_supT χ)).2 w

/-- `Σ_γ |χ(γz)|² ≤ (sup|χ| μ)²`: the support of `χ` meets every orbit at most `μ²` times. -/
structure CutB (χ : testFn) (μ : ℝ) : Prop where
  nonneg : 0 ≤ μ
  bound : ∀ z : ℍ, ∑' γ : Γ, ‖(χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ)‖ₑ ^ 2 ≤ ENNReal.ofReal ((supT χ * μ) ^ 2)

variable {Γ}

lemma tsum_chi_le {χ : testFn} (hinj : InjT Γ χ) (z : ℍ) :
    ∑' γ : Γ, ‖(χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ)‖ₑ ^ 2 ≤ ENNReal.ofReal (supT χ ^ 2) := by
  have hbd : ∀ w : ℂ, ‖(χ : ℂ → ℂ) w‖ₑ ^ 2 ≤ ENNReal.ofReal (supT χ ^ 2) := fun w => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_le_supT χ w) 2)
  by_cases hall : ∀ γ : Γ, (χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ) = 0
  · simp [hall]
  · push_neg at hall
    obtain ⟨γ₀, h₀⟩ := hall
    rw [tsum_eq_single γ₀ fun γ hγ => ?_]
    · exact hbd _
    · have hne : γ * γ₀⁻¹ ≠ 1 := fun h => hγ (mul_inv_eq_one.1 h)
      have := hinj (γ₀ • z) (γ * γ₀⁻¹) hne h₀
      rw [← mul_smul, inv_mul_cancel_right] at this
      rw [this]
      simp

/-- Injective supports cost no factor. -/
lemma cutB_of_injT {χ : testFn} (hinj : InjT Γ χ) : CutB Γ χ 1 :=
  ⟨zero_le_one, fun z => by rw [mul_one]; exact tsum_chi_le hinj z⟩

lemma lint_cut_le {χ : testFn} {μ : ℝ} (hc : CutB Γ χ μ) (u : L2M) :
    ∫⁻ z : ℍ, ‖(χ : ℂ → ℂ) z * liftM Γ u z‖ₑ ^ 2 ≤ ENNReal.ofReal ((supT χ * μ) ^ 2 * ‖u‖ ^ 2) := by
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have hχm : Measurable fun z : ℍ => (χ : ℂ → ℂ) z := (χ.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).measurable
  have hm : Measurable fun z : ℍ => ‖(χ : ℂ → ℂ) z * liftM Γ u z‖ₑ ^ 2 := ((hχm.mul (measurable_liftM Γ u)).enorm).pow_const 2
  rw [lintegral_eq_lintegral_automorphize Γ hF hm, ENNReal.ofReal_mul (by positivity), ← lintegral_enorm_sq_eq,
    ← lintegral_const_mul _ ((Lp.stronglyMeasurable u).measurable.enorm.pow_const 2)]
  refine lintegral_mono fun x => ?_
  induction x using Quotient.inductionOn with | _ z
  show ∑' γ : Γ, ‖(χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ) * liftM Γ u (γ • z)‖ₑ ^ 2 ≤ ENNReal.ofReal ((supT χ * μ) ^ 2) * ‖(u : Surf Γ → ℂ) (surfMk Γ z)‖ₑ ^ 2
  simp_rw [liftM_smul, enorm_mul, mul_pow]
  rw [ENNReal.tsum_mul_right]
  have hb := hc.bound z
  rw [mul_pow] at hb
  exact mul_le_mul_left hb _

lemma memLp_cut {χ : testFn} {μ : ℝ} (hc : CutB Γ χ μ) (u : L2M) :
    MemLp (fun z : ℍ => (χ : ℂ → ℂ) z * liftM Γ u z) 2 (volume : Measure ℍ) := by
  have hχm : Measurable fun z : ℍ => (χ : ℂ → ℂ) z := (χ.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).measurable
  have hm : AEStronglyMeasurable (fun z : ℍ => (χ : ℂ → ℂ) z * liftM Γ u z) volume := (hχm.mul (measurable_liftM Γ u)).aestronglyMeasurable
  have e := eLpNorm_two_le_of_lintegral_sq_le hm (a := supT χ * μ * ‖u‖) (by have := supT_nonneg χ; have := hc.nonneg; positivity)
    (by rw [mul_pow]; exact lint_cut_le hc u)
  exact e.trans_lt ENNReal.ofReal_lt_top

/-- `χ ũ ∈ L²(ℍ)`. -/
noncomputable def cutV {χ : testFn} {μ : ℝ} (hc : CutB Γ χ μ) (u : L2M) : L2H' := (memLp_cut hc u).toLp _

lemma cutV_ae {χ : testFn} {μ : ℝ} (hc : CutB Γ χ μ) (u : L2M) : ⇑(cutV hc u) =ᵐ[volume] fun z : ℍ => (χ : ℂ → ℂ) z * liftM Γ u z :=
  (memLp_cut hc u).coeFn_toLp

lemma norm_cutV_le {χ : testFn} {μ : ℝ} (hc : CutB Γ χ μ) (u : L2M) : ‖cutV hc u‖ ≤ supT χ * μ * ‖u‖ := by
  have h := lint_cut_le hc u
  have e : ∫⁻ z : ℍ, ‖(cutV hc u : L2H') z‖ₑ ^ 2 ≤ ENNReal.ofReal ((supT χ * μ) ^ 2 * ‖u‖ ^ 2) := by
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr_ae ?_
    filter_upwards [cutV_ae hc u] with z hz
    rw [hz]
  rw [lintegral_enorm_sq_eq] at e
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e
  rw [← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := supT_nonneg χ; have := hc.nonneg; positivity) two_ne_zero).1 h2

/-- **The pairing on `ℍ` is the pairing on `M`.** -/
theorem cut_pair {χ : testFn} {μ : ℝ} (hχ : IsRealT χ) (hinj : CutB Γ χ μ) (u : L2M) (P : testFn) :
    ⟪toL2 P, cutV hinj u⟫_ℂ = ⟪perioT Γ (mulT χ P), u⟫_ℂ := by
  rw [← inner_conj_symm (perioT Γ (mulT χ P)) u]
  show _ = (starRingEnd ℂ) ⟪u, perioL2 Γ (continuous_tfn (mulT χ P)) (hasCompactSupport_tfn (mulT χ P))⟫_ℂ
  rw [inner_perioL2_left, ← integral_conj, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toL2_ae P, cutV_ae hinj u] with z h1 h2
  rw [h1, h2]
  have hr : (starRingEnd ℂ) ((χ : ℂ → ℂ) (z : ℂ)) = (χ : ℂ → ℂ) z := hχ _
  show inner ℂ ((P : ℂ → ℂ) z) ((χ : ℂ → ℂ) z * liftM Γ u z) = (starRingEnd ℂ) ((starRingEnd ℂ) (liftM Γ u z) * ((χ : ℂ → ℂ) z * (P : ℂ → ℂ) z))
  rw [RCLike.inner_apply]
  simp only [map_mul, Complex.conj_conj, hr]
  ring

/-- The weak equation on test functions. -/
theorem weak_tests (u : (negLapMH Γ).domain) (Q : testFn) :
    ⟪perioT Γ (lapTest Q), (u : L2M)⟫_ℂ = -⟪perioT Γ Q, negLapMH Γ u⟫_ℂ := by
  have hQ := perioT_mem_negLapM_domain Γ Q
  have h1 := (negLapMH_isPositive Γ).1 ⟨perioT Γ Q, perioT_mem_negLapMH_domain Γ Q⟩ u
  have h2 : negLapMH Γ ⟨perioT Γ Q, perioT_mem_negLapMH_domain Γ Q⟩ = -perioT Γ (lapTest Q) := by
    rw [← negLapM_apply Γ Q hQ]
    exact ((negLapM_le_negLapMH Γ).2 rfl).symm
  rw [h2, inner_neg_left] at h1
  have h3 : ⟪perioT Γ Q, negLapMH Γ u⟫_ℂ = -⟪perioT Γ (lapTest Q), (u : L2M)⟫_ℂ := h1
  rw [h3, neg_neg]

end cut

end Qschubert
