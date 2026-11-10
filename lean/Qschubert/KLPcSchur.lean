import Qschubert.KLPcCWc

/-!
# From block bounds on shells to a weighted bound, and the transfer lemma

`shell_schur`: an additive bounded map `T` of `L²(ℍ)` whose blocks `1_l T 1_n` on the shells `{⌊ψ⌋ = n}` are bounded by a kernel with bounded
row and column sums is bounded in every weight comparable to constants on the shells.

`transfer`: if `‖T u‖ ≤ M₀ ‖u‖` and `e^{βl} ‖1_l T u‖ ≤ M₁ e^{β(n+1)} ‖u‖` for `u` supported in the shell `n` (`β > 1/2`, `M₀ ≤ M₁`), then
`‖ω T f‖ ≤ K M₀^{1-t} M₁^t ‖ω f‖` for `ω ≍ e^{ψ/2} (1 + ψ)^c`, `0 ≤ c ≤ 1`, with `t = (1 + 1/(2β))/2`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal InnerProductSpace UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section additive

variable {T : L2H' → L2H'} (hadd : ∀ u v, T (u + v) = T u + T v) {M₀ : ℝ} (hbd : ∀ u, ‖T u‖ ≤ M₀ * ‖u‖)

include hbd in
lemma addmap_zero : T 0 = 0 := by
  have h := hbd 0
  rw [norm_zero, mul_zero] at h
  exact norm_le_zero_iff.1 h

include hadd hbd in
lemma addmap_sum (s : Finset ℕ) (g : ℕ → L2H') : T (∑ n ∈ s, g n) = ∑ n ∈ s, T (g n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [addmap_zero hbd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

include hadd in
lemma addmap_sub (u v : L2H') : T (u - v) = T u - T v := by
  have h := hadd (u - v) v
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

include hadd hbd in
lemma addmap_tendsto {F : ℕ → L2H'} {f : L2H'} (h : Tendsto F atTop (𝓝 f)) : Tendsto (fun N => T (F N)) atTop (𝓝 (T f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  have h2 : Tendsto (fun N => |M₀| * ‖F N - f‖) atTop (𝓝 0) := by
    have := h.const_mul |M₀|
    rwa [mul_zero] at this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) h2
  rw [← addmap_sub hadd]
  exact (hbd _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))

end additive

/-- **Schur test on the shells.** -/
theorem shell_schur {om : UpperHalfPlane → ℝ} (hom : ∀ z, 0 ≤ om z) {ωl ωh : ℕ → ℝ} (hωl0 : ∀ n, 0 < ωl n) (hωh0 : ∀ l, 0 < ωh l)
    (hlo : ∀ (n : ℕ) (z : UpperHalfPlane), z ∈ shell n → ωl n ≤ om z)
    (hhi : ∀ (l : ℕ) (z : UpperHalfPlane), z ∈ shell l → om z ≤ ωh l)
    {T : L2H' → L2H'} (hadd : ∀ u v, T (u + v) = T u + T v) {M₀ : ℝ} (hbd : ∀ u, ‖T u‖ ≤ M₀ * ‖u‖)
    {B : ℕ → ℕ → ℝ} (hB0 : ∀ l n, 0 ≤ B l n) {C₁ C₂ : ℝ} (hC1 : 0 ≤ C₁) (hC2 : 0 ≤ C₂)
    (h1 : ∀ l N, ∑ n ∈ Finset.range N, B l n ≤ C₁) (h2 : ∀ n L, ∑ l ∈ Finset.range L, B l n ≤ C₂)
    (hblock : ∀ (l n : ℕ) (f : L2H'), ωh l * ‖cutN l (T (cutN n f))‖ ≤ B l n * (ωl n * ‖cutN n f‖)) (f : L2H') :
    ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖T f z‖ ^ 2) ≤ ENNReal.ofReal (C₁ * C₂) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  set W := ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) with hW
  set a : ℕ → ℝ := fun n => ωl n * ‖cutN n f‖ with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (hωl0 n).le (norm_nonneg _)
  set F : ℕ → L2H' := fun N => ∑ n ∈ Finset.range N, cutN n f with hF
  have hsum : ∀ (N l : ℕ), ωh l * ‖cutN l (T (F N))‖ ≤ ∑ n ∈ Finset.range N, B l n * a n := fun N l => by
    have e : cutN l (T (F N)) = ∑ n ∈ Finset.range N, cutN l (T (cutN n f)) := by
      simp only [hF]
      rw [addmap_sum hadd hbd, map_sum]
    rw [e]
    calc _ ≤ ωh l * ∑ n ∈ Finset.range N, ‖cutN l (T (cutN n f))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hωh0 l).le
      _ = ∑ n ∈ Finset.range N, ωh l * ‖cutN l (T (cutN n f))‖ := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun n _ => hblock l n f
  have hsch : ∀ N L : ℕ, ∑ l ∈ Finset.range L, (∑ n ∈ Finset.range N, B l n * a n) ^ 2
      ≤ C₁ * C₂ * ∑ n ∈ Finset.range N, a n ^ 2 := fun N L => by
    refine schur_finite (p := fun _ => 1) hB0 (fun _ => one_pos) (fun l => ?_) (fun n => ?_) hC1
    · simpa using h1 l N
    · simpa using h2 n L
  by_cases hWt : W = ⊤
  · by_cases hC : C₁ * C₂ = 0
    · -- every block vanishes
      have hz : ∀ N L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T (F N))‖) ^ 2 ≤ 0 := fun N L => by
        calc _ ≤ ∑ l ∈ Finset.range L, (∑ n ∈ Finset.range N, B l n * a n) ^ 2 :=
              Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (mul_nonneg (hωh0 l).le (norm_nonneg _)) (hsum N l) 2
          _ ≤ C₁ * C₂ * ∑ n ∈ Finset.range N, a n ^ 2 := hsch N L
          _ = 0 := by rw [hC, zero_mul]
      have hlim0 : ∀ L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T f)‖) ^ 2 ≤ 0 := fun L => by
        have ht1 : Tendsto (fun N : ℕ => ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T (F N))‖) ^ 2) atTop
            (𝓝 (∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T f)‖) ^ 2)) := by
          refine tendsto_finsetSum _ fun l _ => ?_
          have h1' : Tendsto (fun N : ℕ => cutN l (T (F N))) atTop (𝓝 (cutN l (T f))) :=
            ((cutN l).continuous.tendsto _).comp (addmap_tendsto hadd hbd (tendsto_sum_cutN f))
          exact (h1'.norm.const_mul _).pow 2
        exact le_of_tendsto' ht1 fun N => hz N L
      have hcut0 : ∀ l, cutN l (T f) = 0 := fun l => by
        have h := hlim0 (l + 1)
        have hnn : ∀ i ∈ Finset.range (l + 1), 0 ≤ (ωh i * ‖cutN i (T f)‖) ^ 2 := fun i _ => by positivity
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h (Finset.sum_nonneg hnn)) l (Finset.self_mem_range_succ l)
        have h3 : ωh l * ‖cutN l (T f)‖ = 0 := by simpa using h0
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (hωh0 l).ne'
        · exact norm_eq_zero.1 h4
      have hTf : T f = 0 := by
        have ht := tendsto_sum_cutN (T f)
        have e : (fun N : ℕ => ∑ n ∈ Finset.range N, cutN n (T f)) = fun _ => 0 := by
          funext N
          exact Finset.sum_eq_zero fun n _ => hcut0 n
        rw [e] at ht
        exact (tendsto_nhds_unique ht tendsto_const_nhds)
      rw [hTf]
      have hz' : ∀ᵐ z : UpperHalfPlane, ENNReal.ofReal (om z ^ 2 * ‖(0 : L2H') z‖ ^ 2) = 0 := by
        filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure UpperHalfPlane)] with z hz
        rw [hz]
        simp
      rw [lintegral_congr_ae hz']
      simp
    · rw [hWt, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact lt_of_le_of_ne (mul_nonneg hC1 hC2) (Ne.symm hC)
  have hsumW : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ^ 2 ≤ W.toReal := fun N => by
    rw [← ENNReal.ofReal_le_iff_le_toReal hWt, ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity]
    calc ∑ n ∈ Finset.range N, ENNReal.ofReal (a n ^ 2)
        ≤ ∑ n ∈ Finset.range N, ∫⁻ z in shell n, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h := shell_lower (om := om) (hωl0 n).le (fun z hz => hlo n z hz) f
          have e : a n ^ 2 = ωl n ^ 2 * ‖cutN n f‖ ^ 2 := by simp only [ha]; ring
          rw [e]
          exact h
      _ = ∫⁻ z in ⋃ n ∈ Finset.range N, shell n, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) :=
          (lintegral_biUnion_finset (fun a _ b _ hab => shell_disjoint hab) (fun n _ => measurableSet_shell n) _).symm
      _ ≤ W := setLIntegral_le_lintegral _ _
  set Q := C₁ * C₂ with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hC1 hC2
  have hfin : ∀ N L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T (F N))‖) ^ 2 ≤ Q * W.toReal := fun N L => by
    calc _ ≤ ∑ l ∈ Finset.range L, (∑ n ∈ Finset.range N, B l n * a n) ^ 2 :=
          Finset.sum_le_sum fun l _ =>
            pow_le_pow_left₀ (mul_nonneg (hωh0 l).le (norm_nonneg _)) (hsum N l) 2
      _ ≤ Q * ∑ n ∈ Finset.range N, a n ^ 2 := hsch N L
      _ ≤ Q * W.toReal := mul_le_mul_of_nonneg_left (hsumW N) hQ0
  set v := T f with hv
  have hlim : ∀ L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2 ≤ Q * W.toReal := fun L => by
    have ht1 : Tendsto (fun N : ℕ => ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (T (F N))‖) ^ 2) atTop
        (𝓝 (∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2)) := by
      refine tendsto_finsetSum _ fun l _ => ?_
      have h1' : Tendsto (fun N : ℕ => cutN l (T (F N))) atTop (𝓝 (cutN l v)) :=
        ((cutN l).continuous.tendsto _).comp (addmap_tendsto hadd hbd (tendsto_sum_cutN f))
      exact (h1'.norm.const_mul _).pow 2
    exact le_of_tendsto' ht1 fun N => hfin N L
  have hunion : (⋃ l, shell l) = (univ : Set UpperHalfPlane) := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨_, rfl⟩
  have htot : ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) = ∑' l, ∫⁻ z in shell l, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) := by
    rw [← lintegral_iUnion measurableSet_shell shell_disjoint, hunion, Measure.restrict_univ]
  rw [htot]
  refine ENNReal.tsum_le_of_sum_range_le fun L => ?_
  calc ∑ l ∈ Finset.range L, ∫⁻ z in shell l, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2)
      ≤ ∑ l ∈ Finset.range L, ENNReal.ofReal (ωh l ^ 2 * ‖cutN l v‖ ^ 2) :=
        Finset.sum_le_sum fun l _ => shell_upper hom (fun z hz => hhi l z hz) v
    _ = ENNReal.ofReal (∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun l _ => by positivity]
        exact Finset.sum_congr rfl fun l _ => by rw [← mul_pow]
    _ ≤ ENNReal.ofReal (Q * W.toReal) := ENNReal.ofReal_le_ofReal (hlim L)
    _ = _ := by
        rw [ENNReal.ofReal_mul hQ0, ENNReal.ofReal_toReal hWt]

/-- `min(a, b) ≤ a^{1-t} b^t`. -/
lemma le_rpow_mul_rpow {a b x t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hxa : x ≤ a) (hxb : x ≤ b) :
    x ≤ a ^ (1 - t) * b ^ t := by
  rcases le_total a b with h | h
  · have e : a = a ^ (1 - t) * a ^ t := by
      rw [← Real.rpow_add' ha (by norm_num), sub_add_cancel, Real.rpow_one]
    calc x ≤ a := hxa
      _ = a ^ (1 - t) * a ^ t := e
      _ ≤ a ^ (1 - t) * b ^ t := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h ht0) (Real.rpow_nonneg ha _)
  · have e : b = b ^ (1 - t) * b ^ t := by
      rw [← Real.rpow_add' hb (by norm_num), sub_add_cancel, Real.rpow_one]
    calc x ≤ b := hxb
      _ = b ^ (1 - t) * b ^ t := e
      _ ≤ a ^ (1 - t) * b ^ t := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb h (by linarith)) (Real.rpow_nonneg hb _)

/-- The kernel `(1 + k) e^{-ηk}`. -/
noncomputable def phiE (η : ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) * Real.exp (-(η * k))

lemma phiE_nonneg (η : ℝ) (k : ℕ) : 0 ≤ phiE η k := by
  unfold phiE
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  positivity

lemma summable_phiE {η : ℝ} (hη : 0 < η) : Summable (phiE η) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hη
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hη
  have e : phiE η = fun n : ℕ => (n : ℝ) ^ 0 * Real.exp (-η * n) + (n : ℝ) ^ 1 * Real.exp (-η * n) := by
    funext n
    unfold phiE
    rw [pow_zero, pow_one, neg_mul]
    ring
  rw [e]
  exact h0.add h1

set_option maxHeartbeats 1600000 in
/-- **The transfer lemma.** -/
theorem transfer {β c D : ℝ} (hβ : 1 / 2 < β) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (om : UpperHalfPlane → ℝ), (∀ z, 0 ≤ om z) →
      (∀ (n : ℕ) (z : UpperHalfPlane), z ∈ shell n → Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ om z) →
      (∀ (l : ℕ) (z : UpperHalfPlane), z ∈ shell l → om z ≤ D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c) →
      ∀ (T : L2H' → L2H'), (∀ u v, T (u + v) = T u + T v) → ∀ {M₀ M₁ : ℝ}, 0 ≤ M₀ → M₀ ≤ M₁ → (∀ u, ‖T u‖ ≤ M₀ * ‖u‖) →
      (∀ (l n : ℕ) (u : L2H'), cutN n u = u → Real.exp (β * l) * ‖cutN l (T u)‖ ≤ M₁ * Real.exp (β * (n + 1)) * ‖u‖) →
      ∀ f : L2H', ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖T f z‖ ^ 2)
        ≤ ENNReal.ofReal ((K * (M₀ ^ (1 - (1 + 1 / (2 * β)) / 2) * M₁ ^ ((1 + 1 / (2 * β)) / 2))) ^ 2)
          * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  set t : ℝ := (1 + 1 / (2 * β)) / 2 with htd
  have hβ0 : 0 < β := by linarith
  have ht0 : 0 < t := by rw [htd]; positivity
  have ht1 : t < 1 := by
    rw [htd]
    have : 1 / (2 * β) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hβt : β * t = β / 2 + 1 / 4 := by rw [htd]; field_simp; ring
  set η : ℝ := min ((β - 1 / 2) / 2) (1 / 2) with hηd
  have hη0 : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ β * t - 1 / 2 := by rw [hβt]; exact (min_le_left _ _).trans (by linarith)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  set Z := ∑' k, phiE η k with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (phiE_nonneg η)
  set Λ : ℝ := D * Real.exp (β * t) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  refine ⟨Λ * (2 * Z) + 1, by positivity, fun om hom hlo hhi T hadd M₀ M₁ hM0 hM01 hbd hw f => ?_⟩
  have hM1 : 0 ≤ M₁ := hM0.trans hM01
  set G : ℝ := M₀ ^ (1 - t) * M₁ ^ t with hG
  have hG0 : 0 ≤ G := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
  set ωl : ℕ → ℝ := fun n => Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c with hωl
  set ωh : ℕ → ℝ := fun l => D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c with hωh
  have hωl0 : ∀ n, 0 < ωl n := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hωl]
    have h1 : 0 < (1 + (n : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hωh0 : ∀ l, 0 < ωh l := fun l => by
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    simp only [hωh]
    have h1 : 0 < (1 + (l : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    positivity
  set B : ℕ → ℕ → ℝ := fun l n => G * Λ * phiE η (kd l n) with hB
  have hB0 : ∀ l n, 0 ≤ B l n := fun l n => mul_nonneg (by positivity) (phiE_nonneg η _)
  have hsum1 : ∀ l N, ∑ n ∈ Finset.range N, B l n ≤ G * Λ * (2 * Z) := fun l N => by
    have h := sum_kd_le (phiE_nonneg η) (summable_phiE hη0) l N
    calc ∑ n ∈ Finset.range N, B l n = G * Λ * ∑ n ∈ Finset.range N, phiE η (kd l n) := by
          rw [Finset.mul_sum]
      _ ≤ G * Λ * (2 * Z) := mul_le_mul_of_nonneg_left h (by positivity)
  have hsum2 : ∀ n L, ∑ l ∈ Finset.range L, B l n ≤ G * Λ * (2 * Z) := fun n L => by
    have h := sum_kd_le (phiE_nonneg η) (summable_phiE hη0) n L
    calc ∑ l ∈ Finset.range L, B l n = G * Λ * ∑ l ∈ Finset.range L, phiE η (kd n l) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by simp only [hB]; rw [kd_comm]
      _ ≤ G * Λ * (2 * Z) := mul_le_mul_of_nonneg_left h (by positivity)
  have hblock : ∀ (l n : ℕ) (g : L2H'), ωh l * ‖cutN l (T (cutN n g))‖ ≤ B l n * (ωl n * ‖cutN n g‖) := fun l n g => by
    set u := cutN n g with hu
    have hid : cutN n u = u := cutN_idem n g
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hun : 0 ≤ ‖u‖ := norm_nonneg _
    have hEn := Real.exp_pos ((n : ℝ) / 2)
    have hn1 : 0 < (1 + (n : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    have hl1 : 0 < (1 + (l : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    have hk0 : (0 : ℝ) ≤ kd l n := Nat.cast_nonneg _
    have hb0 : ‖cutN l (T u)‖ ≤ M₀ * ‖u‖ := (norm_cutN_le l _).trans (hbd u)
    rcases le_or_gt l n with hln | hln
    · -- `l ≤ n`
      have hkd : (kd l n : ℝ) = (n : ℝ) - l := by
        unfold kd
        have e : l - n = 0 := by omega
        rw [e, zero_add, Nat.cast_sub hln]
      have hlnR : (l : ℝ) ≤ n := by exact_mod_cast hln
      have hpow : (1 + (l : ℝ)) ^ c ≤ (1 + (n : ℝ)) ^ c := Real.rpow_le_rpow (by linarith) (by linarith) hc0
      have hMG : M₀ ≤ G := by
        have e : M₀ = M₀ ^ (1 - t) * M₀ ^ t := by
          rw [← Real.rpow_add' hM0 (by norm_num), sub_add_cancel, Real.rpow_one]
        calc M₀ = M₀ ^ (1 - t) * M₀ ^ t := e
          _ ≤ M₀ ^ (1 - t) * M₁ ^ t := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0 hM01 ht0.le) (Real.rpow_nonneg hM0 _)
      have hexp : Real.exp ((l : ℝ) / 2) ≤ Real.exp ((n : ℝ) / 2) * Real.exp (-(η * kd l n)) := by
        rw [← Real.exp_add, hkd]
        refine Real.exp_le_exp.2 ?_
        nlinarith
      have hphi : Real.exp (-(η * kd l n)) ≤ phiE η (kd l n) := by
        unfold phiE
        have := Real.exp_pos (-(η * (kd l n : ℝ)))
        nlinarith
      have hE1 : (1 : ℝ) ≤ Real.exp (β * t) := Real.one_le_exp (by positivity)
      calc ωh l * ‖cutN l (T u)‖ ≤ ωh l * (M₀ * ‖u‖) := mul_le_mul_of_nonneg_left hb0 (hωh0 l).le
        _ = D * (Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c) * (M₀ * ‖u‖) := by simp only [hωh]; ring
        _ ≤ D * ((Real.exp ((n : ℝ) / 2) * phiE η (kd l n)) * (1 + (n : ℝ)) ^ c) * (G * ‖u‖) := by
            have h1 : Real.exp ((l : ℝ) / 2) ≤ Real.exp ((n : ℝ) / 2) * phiE η (kd l n) :=
              hexp.trans (mul_le_mul_of_nonneg_left hphi hEn.le)
            have h2 : Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c ≤ (Real.exp ((n : ℝ) / 2) * phiE η (kd l n)) * (1 + (n : ℝ)) ^ c :=
              mul_le_mul h1 hpow hl1.le (mul_nonneg hEn.le (phiE_nonneg η _))
            have h3 : M₀ * ‖u‖ ≤ G * ‖u‖ := mul_le_mul_of_nonneg_right hMG hun
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hD.le) h3 (mul_nonneg hM0 hun)
              (mul_nonneg hD.le (mul_nonneg (mul_nonneg hEn.le (phiE_nonneg η _)) hn1.le))
        _ ≤ G * (D * Real.exp (β * t)) * phiE η (kd l n) * (ωl n * ‖u‖) := by
            have e : D * ((Real.exp ((n : ℝ) / 2) * phiE η (kd l n)) * (1 + (n : ℝ)) ^ c) * (G * ‖u‖)
                = (G * D * phiE η (kd l n) * (ωl n * ‖u‖)) * 1 := by simp only [hωl]; ring
            have e2 : G * (D * Real.exp (β * t)) * phiE η (kd l n) * (ωl n * ‖u‖)
                = (G * D * phiE η (kd l n) * (ωl n * ‖u‖)) * Real.exp (β * t) := by ring
            rw [e, e2]
            exact mul_le_mul_of_nonneg_left hE1
              (mul_nonneg (mul_nonneg (mul_nonneg hG0 hD.le) (phiE_nonneg η _)) (mul_nonneg (hωl0 n).le hun))
    · -- `n < l`
      have hnl : n ≤ l := hln.le
      have hkd : (kd l n : ℝ) = (l : ℝ) - n := by
        unfold kd
        have e : n - l = 0 := by omega
        rw [e, add_zero, Nat.cast_sub hnl]
      have hnlR : (n : ℝ) ≤ l := by exact_mod_cast hnl
      have hw' := hw l n u hid
      have hEl := Real.exp_pos (β * (l : ℝ))
      have hb1 : ‖cutN l (T u)‖ ≤ M₁ * Real.exp (β - β * kd l n) * ‖u‖ := by
        have e : M₁ * Real.exp (β * ((n : ℝ) + 1)) * ‖u‖ = Real.exp (β * l) * (M₁ * Real.exp (β - β * kd l n) * ‖u‖) := by
          have e3 : Real.exp (β * ((n : ℝ) + 1)) = Real.exp (β * l) * Real.exp (β - β * kd l n) := by
            rw [← Real.exp_add, hkd]
            congr 1
            ring
          rw [e3]
          ring
        rw [e] at hw'
        exact le_of_mul_le_mul_left hw' hEl
      have hx0 : 0 ≤ M₁ * Real.exp (β - β * kd l n) := mul_nonneg hM1 (Real.exp_pos _).le
      have hmin : ‖cutN l (T u)‖ ≤ (M₀ ^ (1 - t) * (M₁ * Real.exp (β - β * kd l n)) ^ t) * ‖u‖ := by
        rcases eq_or_lt_of_le hun with h0 | hpos
        · have hz : ‖cutN l (T u)‖ ≤ 0 := by
            have := hb0
            rw [← h0, mul_zero] at this
            exact this
          rw [← h0, mul_zero]
          exact hz
        · have h1 : ‖cutN l (T u)‖ / ‖u‖ ≤ M₀ := by rw [div_le_iff₀ hpos]; exact hb0
          have h2 : ‖cutN l (T u)‖ / ‖u‖ ≤ M₁ * Real.exp (β - β * kd l n) := by rw [div_le_iff₀ hpos]; exact hb1
          have h3 := le_rpow_mul_rpow hM0 hx0 ht0.le ht1.le h1 h2
          rwa [div_le_iff₀ hpos] at h3
      have e4 : (M₁ * Real.exp (β - β * kd l n)) ^ t = M₁ ^ t * Real.exp (β * t) * Real.exp (-(β * t * kd l n)) := by
        rw [Real.mul_rpow hM1 (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      have hratio : (1 + (l : ℝ)) ^ c ≤ (1 + (kd l n : ℝ)) * (1 + (n : ℝ)) ^ c := by
        have h1 : (1 + (l : ℝ)) ≤ (1 + (kd l n : ℝ)) * (1 + (n : ℝ)) := by rw [hkd]; nlinarith
        have h2 : (1 + (l : ℝ)) ^ c ≤ ((1 + (kd l n : ℝ)) * (1 + (n : ℝ))) ^ c := Real.rpow_le_rpow (by linarith) h1 hc0
        rw [Real.mul_rpow (by linarith) (by linarith)] at h2
        have h3 : (1 + (kd l n : ℝ)) ^ c ≤ 1 + (kd l n : ℝ) := by
          have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + (kd l n : ℝ) by linarith) hc1
          rwa [Real.rpow_one] at this
        exact h2.trans (mul_le_mul_of_nonneg_right h3 hn1.le)
      have hexp : Real.exp ((l : ℝ) / 2) * Real.exp (-(β * t * kd l n)) ≤ Real.exp ((n : ℝ) / 2) * Real.exp (-(η * kd l n)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have : η * (kd l n : ℝ) ≤ (β * t - 1 / 2) * kd l n := mul_le_mul_of_nonneg_right hη1 hk0
        rw [hkd] at this ⊢
        nlinarith
      have hMt : 0 ≤ M₀ ^ (1 - t) := Real.rpow_nonneg hM0 _
      have hM1t : 0 ≤ M₁ ^ t := Real.rpow_nonneg hM1 _
      have hEb := Real.exp_pos (β * t)
      calc ωh l * ‖cutN l (T u)‖ ≤ ωh l * ((M₀ ^ (1 - t) * (M₁ * Real.exp (β - β * kd l n)) ^ t) * ‖u‖) :=
            mul_le_mul_of_nonneg_left hmin (hωh0 l).le
        _ = (G * D * Real.exp (β * t) * ‖u‖) * ((Real.exp ((l : ℝ) / 2) * Real.exp (-(β * t * kd l n))) * (1 + (l : ℝ)) ^ c) := by
            rw [e4]; simp only [hωh, hG]; ring
        _ ≤ (G * D * Real.exp (β * t) * ‖u‖) * ((Real.exp ((n : ℝ) / 2) * Real.exp (-(η * kd l n))) * ((1 + (kd l n : ℝ)) * (1 + (n : ℝ)) ^ c)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul hexp hratio hl1.le (by positivity)) ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg hG0 hD.le) hEb.le) hun
        _ = B l n * (ωl n * ‖u‖) := by simp only [hB, hωl, hΛ, phiE]; ring
  have hmain := shell_schur hom hωl0 hωh0 hlo hhi hadd hbd hB0 (C₁ := G * Λ * (2 * Z)) (C₂ := G * Λ * (2 * Z)) (by positivity) (by positivity)
    hsum1 hsum2 hblock f
  refine hmain.trans (mul_le_mul_left ?_ _)
  refine ENNReal.ofReal_le_ofReal ?_
  have e : G * Λ * (2 * Z) * (G * Λ * (2 * Z)) = ((Λ * (2 * Z)) * G) ^ 2 := by ring
  rw [e]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hG0

end Qschubert
