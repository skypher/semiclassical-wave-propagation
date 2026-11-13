import Qschubert.KLMainAll

/-!
# The pointwise corollaries with the factor `N^{2N}`

Theorem `pc:main` carries the factor `N^{2N}`; the pointwise corollaries `pc:cor16` and `cor:dd16` were stated with `(2N)!`
(`ptBound`). Since `(2N)! ≤ (2N)^{2N} = 4^N N^{2N}`, the same estimates hold with `N^{2N}` after replacing `C` by `4C`
(`ptBound_le_ptBoundN`). The declarations below restate the six pointwise statements with `ptBoundN`.

* `ptBoundN`, `ptBound_le_ptBoundN`.
* `pccor16_allN`, `pccor16bg_allN`: Corollary `pc:cor16` (original norm; arbitrary quotient, positive injectivity radius).
* `cor16Rmain_allmultN`, `cor16Rmain_allbgN`: Corollary `cor:dd16`, reversed-weight norm.
* `cor16R_multN`, `cor16R_repN`: Corollary `cor:dd16`, power-weight norm.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups

/-- `C^{N+K+1} N^{2N} K! (αħ)^{-2N-2} (ħt/α²)^{K+1}` (with `N^{2N} = 1` at `N = 0`). -/
noncomputable def ptBoundN (C α ħ' t : ℝ) (K N : ℕ) : ℝ :=
  C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ')⁻¹) ^ (2 * N + 2)
    * (ħ' * t / α ^ 2) ^ (K + 1)

lemma ptBound_le_ptBoundN {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    ptBound C α ħ t K N ≤ ptBoundN (4 * C) α ħ t K N := by
  have hf : ((2 * N).factorial : ℝ) ≤ 4 ^ N * (N : ℝ) ^ (2 * N) := by
    have h1 : (2 * N).factorial ≤ (2 * N) ^ (2 * N) := Nat.factorial_le_pow (2 * N)
    have h2 : ((2 * N : ℕ) : ℝ) ^ (2 * N) = 4 ^ N * (N : ℝ) ^ (2 * N) := by
      push_cast
      rw [mul_pow, pow_mul]
      norm_num
    calc ((2 * N).factorial : ℝ) ≤ (((2 * N) ^ (2 * N) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((2 * N : ℕ) : ℝ) ^ (2 * N) := by push_cast; ring
      _ = 4 ^ N * (N : ℝ) ^ (2 * N) := h2
  have h4 : (4 : ℝ) ^ N ≤ 4 ^ (N + K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hx : 0 ≤ (α * ħ)⁻¹ := by positivity
  have hy : 0 ≤ ħ * t / α ^ 2 := by positivity
  have hR : 0 ≤ (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hCp : 0 ≤ C ^ (N + K + 1) := by positivity
  have hNp : 0 ≤ (N : ℝ) ^ (2 * N) := by positivity
  unfold ptBound ptBoundN
  calc C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)
      = (C ^ (N + K + 1) * ((2 * N).factorial : ℝ)) * ((K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)) := by
        ring
    _ ≤ (C ^ (N + K + 1) * (4 ^ (N + K + 1) * (N : ℝ) ^ (2 * N)))
          * ((K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)) := by
        gcongr
        exact hf.trans (mul_le_mul_of_nonneg_right h4 hNp)
    _ = (4 * C) ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
          * (ħ * t / α ^ 2) ^ (K + 1) := by ring

lemma ptBoundN_nonneg {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    0 ≤ ptBoundN C α ħ t K N := by
  unfold ptBoundN
  have := inv_pos.2 (mul_pos hα hħ)
  positivity

/-- The bound `C · m(z)^{1/2} · ptBound C` is at most `4C · m(z)^{1/2} · ptBoundN (4C)`. -/
lemma mult_bound_le {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) (m n : ℝ≥0∞) :
    ENNReal.ofReal C * m * ENNReal.ofReal (ptBound C α ħ t K N) * n
      ≤ ENNReal.ofReal (4 * C) * m * ENNReal.ofReal (ptBoundN (4 * C) α ħ t K N) * n := by
  gcongr
  · linarith
  · exact ptBound_le_ptBoundN K N hC hα hħ ht

/-- **Corollary `pc:cor16`, every quotient, factor `N^{2N}`.** -/
def Stmt_pccor16_allN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_allN : Stmt_pccor16_allN := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16_all Γ hOr x₀ β κ A hβ hκ
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-- **Corollary `cor:dd16`, reversed-weight norm, every quotient, factor `N^{2N}`**, every range `0 < α ≤ A`. -/
def Stmt_cor16Rmain_allmultN : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allmultN : Stmt_cor16Rmain_allmultN := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := cor16Rmain_allmult β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  refine ⟨4 * C, by positivity, fun Γ _ hOr hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-- **Corollary `cor:dd16`, power-weight norm, every quotient, factor `N^{2N}`.** -/
def Stmt_cor16R_multN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_multN : Stmt_cor16R_multN := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := cor16R_mult Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-! ### Positive injectivity radius -/

/-- **The local multiplicity under a positive injectivity radius** (proof of Corollary `pc:cor16`): if every `γ ≠ 1` moves
every point by at least `2 r₀`, then `m(z) ≤ M` with `M` depending only on `r₀`. The orbit points `γ z` with `d(z, γ z) < 2`
are `2 r₀`-separated, so disjoint `r₀`-balls around them fit in `B(z, 2 + r₀)`. -/
theorem multM_le_of_injRad {r₀ : ℝ} (hr₀ : 0 < r₀) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], InjRadGe Γ r₀ →
      ∀ x : Surf Γ, (multM Γ x : ℝ≥0∞) ≤ ENNReal.ofReal M := by
  classical
  have hvfin : volume (Metric.ball UpperHalfPlane.I r₀) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_ball_I_le r₀)
  set v := (volume (Metric.ball UpperHalfPlane.I r₀)).toReal with hv_def
  have hv : 0 < v := ENNReal.toReal_pos (volume_ball_pos UpperHalfPlane.I hr₀).ne' hvfin
  refine ⟨6 * Real.exp (2 + r₀) / v, by positivity, fun Γ _ hinj x => ?_⟩
  set z : ℍ := Quotient.out x
  set A := {γ : Γ | dist z (γ • z) < 2}
  have hA : A.Finite := (finite_near Γ z z 2).subset fun γ hγ => show dist z (γ • z) ≤ 2 from le_of_lt hγ
  set As := hA.toFinset
  set P := As.image (fun γ : Γ => γ • z)
  have hsep : ∀ γ γ' : Γ, γ ≠ γ' → 2 * r₀ ≤ dist (γ • z) (γ' • z) := by
    intro γ γ' hne
    have h1 : γ⁻¹ * γ' ≠ 1 := by
      intro h; apply hne
      have := congrArg (γ * ·) h
      simpa [mul_assoc] using this.symm
    have h2 := hinj (γ⁻¹ * γ') h1 z
    rw [mul_smul, ← dist_smul γ, smul_inv_smul] at h2
    exact h2
  have hinjOn : Set.InjOn (fun γ : Γ => γ • z) (As : Set Γ) := by
    intro γ _ γ' _ h
    by_contra hne
    have := hsep γ γ' hne
    simp only at h
    rw [h, dist_self] at this
    linarith
  have hcard : P.card = As.card := Finset.card_image_of_injOn hinjOn
  have hdisj : (P : Set ℍ).PairwiseDisjoint fun p => Metric.ball p r₀ := by
    intro p hp q hq hpq
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨γ', _, rfl⟩ := Finset.mem_image.1 hq
    refine Metric.ball_disjoint_ball ?_
    have hne : γ ≠ γ' := fun h => hpq (by rw [h])
    linarith [hsep γ γ' hne]
  have hsub : (⋃ p ∈ P, Metric.ball p r₀) ⊆ Metric.ball z (2 + r₀) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨p, hp, hw⟩ := hw
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hp
    have hγ' : dist z (γ • z) < 2 := (Set.Finite.mem_toFinset hA).1 hγ
    rw [Metric.mem_ball] at hw ⊢
    calc dist w z ≤ dist w (γ • z) + dist (γ • z) z := dist_triangle _ _ _
      _ < r₀ + 2 := by rw [dist_comm (γ • z) z]; exact add_lt_add hw hγ'
      _ = 2 + r₀ := add_comm _ _
  have h2 : (P.card : ℝ≥0∞) * volume (Metric.ball UpperHalfPlane.I r₀) ≤ ENNReal.ofReal (6 * Real.exp (2 + r₀)) := by
    calc (P.card : ℝ≥0∞) * volume (Metric.ball UpperHalfPlane.I r₀) = ∑ p ∈ P, volume (Metric.ball p r₀) := by
          rw [Finset.sum_congr rfl fun p _ => volume_ball_eq p r₀, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ p ∈ P, Metric.ball p r₀) :=
          (measure_biUnion_finset hdisj fun p _ => Metric.isOpen_ball.measurableSet).symm
      _ ≤ volume (Metric.ball z (2 + r₀)) := measure_mono hsub
      _ ≤ _ := volume_ball_le z (2 + r₀)
  have h2r : (P.card : ℝ) * v ≤ 6 * Real.exp (2 + r₀) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this
  have hPc : (As.card : ℝ) ≤ 6 * Real.exp (2 + r₀) / v := by
    rw [le_div_iff₀ hv, ← hcard]; exact h2r
  have hm : multM Γ x = (As.card : ℕ∞) := by
    show orbitMult Γ z = _
    unfold orbitMult
    rw [Set.Finite.encard_eq_coe_toFinset_card hA]
  rw [hm, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hPc

lemma ptBoundN_mono {C C₁ α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hCC : C ≤ C₁) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    ptBoundN C α ħ t K N ≤ ptBoundN C₁ α ħ t K N := by
  unfold ptBoundN
  have := inv_pos.2 (mul_pos hα hħ)
  gcongr

/-- Replacing `m(z)^{1/2} ≤ M^{1/2}` in the arbitrary-quotient bound: the constant `C max(1, M^{1/2})` serves both places. -/
lemma bg_bound_le {C M α ħ t : ℝ} (K N : ℕ) (hC : 0 < C) (hM : 0 ≤ M) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t)
    (m : ℕ∞) (hm : (m : ℝ≥0∞) ≤ ENNReal.ofReal M) (n : ℝ≥0∞) :
    ENNReal.ofReal C * ((m : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBoundN C α ħ t K N) * n
      ≤ ENNReal.ofReal (C * max 1 (Real.sqrt M)) * ENNReal.ofReal (ptBoundN (C * max 1 (Real.sqrt M)) α ħ t K N) * n := by
  have hs : (m : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt M) := by
    calc (m : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal M) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hm (by norm_num)
      _ = ENNReal.ofReal (M ^ (1 / 2 : ℝ)) := ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt M) := by rw [Real.sqrt_eq_rpow]
  have hmax : 1 ≤ max 1 (Real.sqrt M) := le_max_left _ _
  have hC1 : C ≤ C * max 1 (Real.sqrt M) := le_mul_of_one_le_right hC.le hmax
  have hCs : C * Real.sqrt M ≤ C * max 1 (Real.sqrt M) := mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le
  calc ENNReal.ofReal C * ((m : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBoundN C α ħ t K N) * n
      ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal (ptBoundN C α ħ t K N) * n := by gcongr
    _ = ENNReal.ofReal (C * Real.sqrt M) * ENNReal.ofReal (ptBoundN C α ħ t K N) * n := by
        rw [ENNReal.ofReal_mul hC.le]
    _ ≤ ENNReal.ofReal (C * max 1 (Real.sqrt M)) * ENNReal.ofReal (ptBoundN (C * max 1 (Real.sqrt M)) α ħ t K N) * n := by
        gcongr
        exact ptBoundN_mono K N hC.le hC1 hα hħ ht

/-- **Corollary `pc:cor16`, positive injectivity radius, factor `N^{2N}`**: `δ` is that of the arbitrary-quotient statement,
chosen before `r₀`; the constant `C`, which also multiplies the bound, depends also on `r₀`. -/
def Stmt_pccor16bg_allN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ r₀ : ℝ, 0 < r₀ → InjRadGe Γ r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_allN : Stmt_pccor16bg_allN := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16_allN Γ hOr x₀ β κ A hβ hκ
  refine ⟨δ, hδ, fun r₀ hr₀ hinj => ?_⟩
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)), fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩

/-- **Corollary `cor:dd16`, reversed-weight norm, positive injectivity radius, factor `N^{2N}`**, every range `0 < α ≤ A`:
`δ` before `P` and `r₀`; `C` after `P` and `r₀`. -/
def Stmt_cor16Rmain_allbgN : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P r₀ : ℝ, 0 < r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allbgN : Stmt_cor16Rmain_allbgN := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := cor16Rmain_allmultN β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P r₀ hr₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)),
    fun Γ _ hOr hP hinj α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩

/-- **Corollary `cor:dd16`, power-weight norm, positive injectivity radius, factor `N^{2N}`**: `δ` before `r₀`. -/
def Stmt_cor16R_repN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ r₀ : ℝ, 0 < r₀ → InjRadGe Γ r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_repN : Stmt_cor16R_repN := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := cor16R_multN Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨δ, hδ, fun r₀ hr₀ hinj => ?_⟩
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)), fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩


end Qschubert
