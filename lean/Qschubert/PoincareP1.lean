import Qschubert.BallVolume
import Qschubert.Statements

/-!
# Lemma P1: `sup_z Σ_γ e^{-s d(x₀, γz)} < ∞` for every Fuchsian `Γ` and `s > 1`

Manuscript `paper.tex`, Appendix "Periodization for every Fuchsian group", Lemma P1. Proof as there:
the orbit `Γx₀` is uniformly separated and its stabilizer is finite (`exists_orbit_sep`,
`finite_stab`), so disjoint balls of a fixed radius around orbit points give
`#{γ : d(z, γx₀) < R} ≤ K e^R` uniformly in `z` (`ncard_orbit_ball_le`), using
`vol B(z, r) = vol B(i, r) ≤ 6 e^r` (`volume_ball_eq`, `volume_ball_I_le`); summing over shells,
`poincareSup Γ x₀ s < ∞` (`poincareSup_lt_top`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real Set Metric
open scoped ENNReal Pointwise MatrixGroups

/-- `g_z = [[y, x], [0, 1]] ∈ GL(2, ℝ)`, with `g_z • i = z`. -/
noncomputable def toPointGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1]
    (by simp [Matrix.det_fin_two]; exact z.im_ne_zero)

lemma toPointGL_det (z : ℍ) : ((toPointGL z).det : ℝ) = z.im := by
  simp [toPointGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

lemma toPointGL_smul_I (z : ℍ) : toPointGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [toPointGL_det]; exact z.im_pos)]
  have h00 : ((toPointGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = z.im := rfl
  have h01 : ((toPointGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = z.re := rfl
  have h10 : ((toPointGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := rfl
  have h11 : ((toPointGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := rfl
  simp only [num, denom, h00, h01, h10, h11]
  apply Complex.ext <;> simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]

/-- Every ball of radius `r` has the volume of `B(i, r)`. -/
lemma volume_ball_eq (z : ℍ) (r : ℝ) : volume (ball z r) = volume (ball I r) := by
  rw [← toPointGL_smul_I z, ← Metric.smul_ball, measure_smul]

lemma volume_ball_le (z : ℍ) (r : ℝ) : volume (ball z r) ≤ ENNReal.ofReal (6 * exp r) := by
  rw [volume_ball_eq]; exact volume_ball_I_le r

lemma volume_ball_pos (z : ℍ) {r : ℝ} (hr : 0 < r) : 0 < volume (ball z r) :=
  isOpen_ball.measure_pos _ (nonempty_ball.2 hr)

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

lemma finite_near (x₀ z : ℍ) (R : ℝ) : {γ : Γ | dist z (γ • x₀) ≤ R}.Finite := by
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (isCompact_singleton (x := x₀))
    (isCompact_closedBall z R)).subset fun γ hγ =>
      ⟨γ • x₀, ⟨x₀, rfl, rfl⟩, by rw [mem_closedBall, dist_comm]; exact hγ⟩

/-- The stabilizer of `x₀` in `Γ` is finite. -/
lemma finite_stab (x₀ : ℍ) : {γ : Γ | γ • x₀ = x₀}.Finite :=
  (finite_near Γ x₀ x₀ 0).subset fun γ hγ => by
    show dist x₀ (γ • x₀) ≤ 0
    rw [show γ • x₀ = x₀ from hγ, dist_self]

/-- **Separation**: `∃ δ > 0`, every `γ` moving `x₀` moves it by at least `δ`. -/
lemma exists_orbit_sep (x₀ : ℍ) : ∃ δ > 0, ∀ γ : Γ, γ • x₀ ≠ x₀ → δ ≤ dist x₀ (γ • x₀) := by
  set T : Set Γ := {γ : Γ | dist x₀ (γ • x₀) ≤ 1 ∧ γ • x₀ ≠ x₀}
  have hT : T.Finite := (finite_near Γ x₀ x₀ 1).subset fun γ hγ => hγ.1
  rcases T.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, fun γ hγ => ?_⟩
    by_contra hlt
    have : γ ∈ T := ⟨(not_le.1 hlt).le, hγ⟩
    rw [h] at this; exact this
  · set m := hT.toFinset.inf' (hT.toFinset_nonempty.2 hne) fun γ => dist x₀ (γ • x₀)
    have hm : 0 < m := by
      rw [Finset.lt_inf'_iff]
      intro γ hγ
      rw [Set.Finite.mem_toFinset] at hγ
      exact dist_pos.2 (Ne.symm hγ.2)
    refine ⟨min 1 m, lt_min one_pos hm, fun γ hγ => ?_⟩
    by_cases h1 : dist x₀ (γ • x₀) ≤ 1
    · exact (min_le_right _ _).trans (Finset.inf'_le _ ((Set.Finite.mem_toFinset hT).2 ⟨h1, hγ⟩))
    · exact (min_le_left _ _).trans (not_le.1 h1).le

/-- **Orbit counting**: `#{γ : d(z, γx₀) < R} ≤ K e^R`, uniformly in `z` and `R`. -/
theorem exists_orbit_count (x₀ : ℍ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℍ) (R : ℝ),
    ({γ : Γ | dist z (γ • x₀) < R}.ncard : ℝ) ≤ K * exp R := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := exists_orbit_sep Γ x₀
  set ρ := δ / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hvfin : volume (ball I ρ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_ball_I_le ρ)
  set v := (volume (ball I ρ)).toReal
  have hv : 0 < v := ENNReal.toReal_pos (volume_ball_pos I hρ).ne' hvfin
  set St := (finite_stab Γ x₀).toFinset
  refine ⟨St.card * 6 * exp ρ / v, by positivity, fun z R => ?_⟩
  set A := {γ : Γ | dist z (γ • x₀) < R}
  have hA : A.Finite := (finite_near Γ x₀ z R).subset fun γ hγ =>
    show dist z (γ • x₀) ≤ R from le_of_lt hγ
  set As := hA.toFinset
  set P := As.image (fun γ : Γ => γ • x₀)
  -- (1) fibres of `γ ↦ γ • x₀` have at most `#Stab` elements
  have h1 : As.card ≤ St.card * P.card := by
    refine Finset.card_le_mul_card_image As St.card fun p hp => ?_
    obtain ⟨γ₁, _, rfl⟩ := Finset.mem_image.1 hp
    refine Finset.card_le_card_of_injOn (fun γ => γ₁⁻¹ * γ) (fun γ hγ => ?_) (fun a _ b _ h => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hγ
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      show (γ₁⁻¹ * γ) • x₀ = x₀
      rw [mul_smul, hγ.2, inv_smul_smul]
    · exact mul_left_cancel h
  -- (2) disjoint `ρ`-balls around the orbit points fit in `B(z, R + ρ)`
  have hdisj : (P : Set ℍ).PairwiseDisjoint fun p => ball p ρ := by
    intro p hp q hq hpq
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨γ', _, rfl⟩ := Finset.mem_image.1 hq
    refine Metric.ball_disjoint_ball ?_
    have hne : (γ⁻¹ * γ') • x₀ ≠ x₀ := by
      intro h; apply hpq
      rw [mul_smul, inv_smul_eq_iff] at h; exact h.symm
    have hd := hsep _ hne
    rw [mul_smul, ← dist_smul γ, smul_inv_smul] at hd
    linarith
  have hsub : (⋃ p ∈ P, ball p ρ) ⊆ ball z (R + ρ) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨p, hp, hw⟩ := hw
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hp
    have hγ' : dist z (γ • x₀) < R := (Set.Finite.mem_toFinset hA).1 hγ
    rw [mem_ball] at hw ⊢
    calc dist w z ≤ dist w (γ • x₀) + dist (γ • x₀) z := dist_triangle _ _ _
      _ < ρ + R := by rw [dist_comm (γ • x₀) z]; exact add_lt_add hw hγ'
      _ = R + ρ := add_comm _ _
  have h2 : (P.card : ℝ≥0∞) * volume (ball I ρ) ≤ ENNReal.ofReal (6 * exp (R + ρ)) := by
    calc (P.card : ℝ≥0∞) * volume (ball I ρ) = ∑ p ∈ P, volume (ball p ρ) := by
          rw [Finset.sum_congr rfl fun p _ => volume_ball_eq p ρ, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ p ∈ P, ball p ρ) := (measure_biUnion_finset hdisj fun p _ => measurableSet_ball).symm
      _ ≤ volume (ball z (R + ρ)) := measure_mono hsub
      _ ≤ _ := volume_ball_le z (R + ρ)
  have h2r : (P.card : ℝ) * v ≤ 6 * exp (R + ρ) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this
  have hPc : (P.card : ℝ) ≤ 6 * exp (R + ρ) / v := by rw [le_div_iff₀ hv]; exact h2r
  rw [Set.ncard_eq_toFinset_card A hA]
  calc (As.card : ℝ) ≤ St.card * P.card := by exact_mod_cast h1
    _ ≤ St.card * (6 * exp (R + ρ) / v) := mul_le_mul_of_nonneg_left hPc (by positivity)
    _ = St.card * 6 * exp ρ / v * exp R := by rw [Real.exp_add]; ring

/-- **Lemma P1.** For every Fuchsian `Γ` (any `Γ ≤ PGL(2, ℝ)` acting properly discontinuously),
every base point `x₀` and every `s > 1`: `sup_z Σ_γ e^{-s d(x₀, γz)} < ∞`. -/
theorem poincareSup_lt_top (x₀ : ℍ) {s : ℝ} (hs : 1 < s) : poincareSup Γ x₀ s < ⊤ := by
  obtain ⟨K, hK0, hK⟩ := exists_orbit_count Γ x₀
  set q := exp (1 - s) with hq_def
  have hq : q < 1 := by
    rw [hq_def]
    calc exp (1 - s) < exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hs0 : 0 < s := by linarith
  suffices h : ∀ z : ℍ, ∑' γ : Γ, ENNReal.ofReal (exp (-(s * dist x₀ (γ • z))))
      ≤ ENNReal.ofReal (K * exp 1 * (1 - q)⁻¹) from
    lt_of_le_of_lt (iSup_le h) ENNReal.ofReal_lt_top
  intro z
  have hre : ∑' γ : Γ, ENNReal.ofReal (exp (-(s * dist x₀ (γ • z))))
      = ∑' γ : Γ, ENNReal.ofReal (exp (-(s * dist z (γ • x₀)))) := by
    rw [← (Equiv.inv Γ).tsum_eq (fun γ : Γ => ENNReal.ofReal (exp (-(s * dist z (γ • x₀)))))]
    congr 1; funext γ
    simp only [Equiv.inv_apply]
    have hd : dist z (γ⁻¹ • x₀) = dist x₀ (γ • z) := by
      rw [← dist_smul γ z (γ⁻¹ • x₀), smul_inv_smul, dist_comm]
    rw [hd]
  rw [hre]
  set A : ℕ → Set Γ := fun n => {γ : Γ | dist z (γ • x₀) < n + 1}
  have hpt : ∀ γ : Γ, ENNReal.ofReal (exp (-(s * dist z (γ • x₀))))
      ≤ ∑' n : ℕ, (A n).indicator (fun _ => ENNReal.ofReal (exp (-(s * n)))) γ := by
    intro γ
    set d := dist z (γ • x₀)
    refine le_trans ?_ (ENNReal.le_tsum ⌊d⌋₊)
    rw [Set.indicator_of_mem (show γ ∈ A ⌊d⌋₊ from Nat.lt_floor_add_one d)]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := Nat.floor_le (dist_nonneg (x := z) (y := γ • x₀))
    nlinarith
  have hcount : ∀ n : ℕ, ∑' γ : Γ, (A n).indicator (fun _ => ENNReal.ofReal (exp (-(s * n)))) γ
      ≤ ENNReal.ofReal (K * exp 1 * q ^ n) := by
    intro n
    have hfin : (A n).Finite := (finite_near Γ x₀ z (n + 1)).subset fun γ hγ =>
      show dist z (γ • x₀) ≤ n + 1 from le_of_lt hγ
    rw [← tsum_subtype, ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
    have hc := hK z (n + 1)
    have e1 : ((((A n).ncard : ℕ∞)) : ℝ≥0∞) = ENNReal.ofReal ((A n).ncard : ℝ) := by
      simp
    rw [e1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e2 : K * exp 1 * q ^ n = K * exp (n + 1) * exp (-(s * n)) := by
      rw [hq_def, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  calc ∑' γ : Γ, ENNReal.ofReal (exp (-(s * dist z (γ • x₀))))
      ≤ ∑' γ : Γ, ∑' n : ℕ, (A n).indicator (fun _ => ENNReal.ofReal (exp (-(s * n)))) γ :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' n : ℕ, ∑' γ : Γ, (A n).indicator (fun _ => ENNReal.ofReal (exp (-(s * n)))) γ :=
        ENNReal.tsum_comm
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (K * exp 1 * q ^ n) := ENNReal.tsum_le_tsum hcount
    _ = ENNReal.ofReal (∑' n : ℕ, K * exp 1 * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((summable_geometric_of_lt_one hq0 hq).mul_left _)).symm
    _ = ENNReal.ofReal (K * exp 1 * (1 - q)⁻¹) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]

end Qschubert
