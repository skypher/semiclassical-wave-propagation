import Qschubert.KLDDMain
import Qschubert.KLConj

/-!
# Theorem 1.4R: the Dyson remainder, and the bridge to the statement
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma two_mul_fact_le (N : ℕ) : ((2 * N).factorial : ℝ) ≤ 4 ^ N * (N : ℝ) ^ (2 * N) := by
  have h : (2 * N).factorial ≤ (2 * N) ^ (2 * N) := Nat.factorial_le_pow _
  have h2 : ((2 * N).factorial : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ (2 * N) := by exact_mod_cast h
  refine h2.trans (le_of_eq ?_)
  push_cast
  rw [mul_pow, pow_mul (2 : ℝ) 2 N]
  norm_num

lemma fact_ratio_le (K : ℕ) : ((2 + 2 * (K + 1)).factorial : ℝ) ≤ 4 * 32 ^ (K + 1) * ((K + 1).factorial : ℝ) * (K.factorial : ℝ) := by
  have e : 2 + 2 * (K + 1) = 2 * (K + 2) := by ring
  rw [e]
  have h1 : (2 * (K + 2)).choose (K + 2) * (K + 2).factorial * (K + 2).factorial = (2 * (K + 2)).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show K + 2 ≤ 2 * (K + 2) by omega)
    rwa [show 2 * (K + 2) - (K + 2) = K + 2 by omega] at this
  have h2 : (2 * (K + 2)).choose (K + 2) ≤ 2 ^ (2 * (K + 2)) := Nat.choose_le_two_pow _ _
  have h3 : (K + 2 : ℝ) ≤ 2 ^ (K + 1) := by
    have : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
    exact_mod_cast this
  have h4 : (K + 1 : ℝ) ≤ 2 ^ (K + 1) := by
    have : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
    exact_mod_cast this.le
  have e2 : ((K + 2).factorial : ℝ) = (K + 2 : ℝ) * ((K + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ (K + 1)]; push_cast; ring
  have e3 : ((K + 1).factorial : ℝ) = (K + 1 : ℝ) * (K.factorial : ℝ) := by
    rw [Nat.factorial_succ K]; push_cast; ring
  have hF : (0 : ℝ) ≤ ((K + 1).factorial : ℝ) := by positivity
  have hG : (0 : ℝ) ≤ (K.factorial : ℝ) := by positivity
  have hc : (((2 * (K + 2)).choose (K + 2) : ℕ) : ℝ) ≤ 4 ^ (K + 2) := by
    have : (((2 * (K + 2)).choose (K + 2) : ℕ) : ℝ) ≤ ((2 ^ (2 * (K + 2)) : ℕ) : ℝ) := by exact_mod_cast h2
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [pow_mul]
    norm_num
  have hK0 : (0 : ℝ) ≤ K + 1 := by positivity
  have hK1 : (0 : ℝ) ≤ K + 2 := by positivity
  calc ((2 * (K + 2)).factorial : ℝ) = (((2 * (K + 2)).choose (K + 2) : ℕ) : ℝ) * ((K + 2).factorial : ℝ) * ((K + 2).factorial : ℝ) := by
        rw [← h1]; push_cast; ring
    _ ≤ 4 ^ (K + 2) * ((K + 2).factorial : ℝ) * ((K + 2).factorial : ℝ) := by gcongr
    _ = 4 ^ (K + 2) * ((K + 2 : ℝ) * (K + 2 : ℝ) * (K + 1 : ℝ)) * (((K + 1).factorial : ℝ) * (K.factorial : ℝ)) := by
        rw [e2]; nth_rewrite 2 [e3]; ring
    _ ≤ 4 ^ (K + 2) * (2 ^ (K + 1) * 2 ^ (K + 1) * 2 ^ (K + 1)) * (((K + 1).factorial : ℝ) * (K.factorial : ℝ)) := by gcongr
    _ = 4 * 32 ^ (K + 1) * ((K + 1).factorial : ℝ) * (K.factorial : ℝ) := by
        have e4 : (32 : ℝ) ^ (K + 1) = 4 ^ (K + 1) * (2 ^ (K + 1) * 2 ^ (K + 1) * 2 ^ (K + 1)) := by
          rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
        rw [e4, pow_succ (4 : ℝ) (K + 1)]
        ring

/-- The last arithmetic step. -/
lemma dd_final {S K₁ Mb C₄ ħ α t FN : ℝ} {K N : ℕ} (hS : 0 ≤ S) (hK₁ : 0 ≤ K₁) (hMb : 1 ≤ Mb) (hC₄ : 1 ≤ C₄) (hħ : 0 < ħ) (hα : 0 < α) (ht : 0 ≤ t) (hFN : 0 ≤ FN) :
    (|ħ| / 2) ^ (K + 1) * ((S * K₁ * (Mb ^ 2) ^ (N + (K + 1)) * C₄ ^ (N + (K + 1) + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * (K + 1)).factorial : ℝ)
        * (α⁻¹) ^ (2 * (K + 1)) * ((α * ħ)⁻¹) ^ (2 * N) * FN) * t ^ (K + 1) / ((K + 1).factorial : ℝ))
      ≤ ddBound ((Mb ^ 2 * C₄ * 128) * (1 + 4 * C₄ ^ 2 * (S * K₁))) α ħ t K N * FN := by
  set m := N + K + 1 with hm
  have hm' : N + (K + 1) = m := by omega
  have hm1 : m ≠ 0 := by omega
  set x := 4 * C₄ ^ 2 * (S * K₁) with hx
  have hx0 : 0 ≤ x := by positivity
  set B₁ := Mb ^ 2 * C₄ * 128 with hB₁
  have hB₁0 : 0 < B₁ := by positivity
  set T := (ħ * t / α ^ 2) ^ (K + 1) with hT
  have hT0 : 0 ≤ T := by positivity
  set X := ((α * ħ)⁻¹) ^ (2 * N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hFk : (0 : ℝ) < ((K + 1).factorial : ℝ) := by positivity
  have hF0 : (0 : ℝ) ≤ (K.factorial : ℝ) := by positivity
  have hNN : (0 : ℝ) ≤ (N : ℝ) ^ (2 * N) := by positivity
  rw [abs_of_pos hħ, hm']
  have eT : (ħ / 2) ^ (K + 1) * (α⁻¹ ^ (2 * (K + 1)) * t ^ (K + 1)) = (1 / 2) ^ (K + 1) * T := by
    rw [hT, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have hcore : (1 / 2 : ℝ) ^ (K + 1) * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * (((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ)))
      ≤ (B₁ * (1 + x)) ^ m * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) := by
    have h1 : ((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ) ≤ 4 * 32 ^ (K + 1) * (K.factorial : ℝ) := by
      rw [div_le_iff₀ hFk]
      refine (fact_ratio_le K).trans (le_of_eq ?_)
      ring
    have h2 := two_mul_fact_le N
    have h3 : (1 / 2 : ℝ) ^ (K + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h4 : (4 : ℝ) ^ N * 32 ^ (K + 1) ≤ 128 ^ m := by
      have : (128 : ℝ) ^ m = 128 ^ N * 128 ^ (K + 1) := by rw [hm, add_assoc, pow_add]
      rw [this]
      have a1 : (4 : ℝ) ^ N ≤ 128 ^ N := pow_le_pow_left₀ (by norm_num) (by norm_num) N
      have a2 : (32 : ℝ) ^ (K + 1) ≤ 128 ^ (K + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      exact mul_le_mul a1 a2 (by positivity) (by positivity)
    have h5 : 1 + x ≤ (1 + x) ^ m := le_self_pow₀ (by linarith) hm1
    have hS1 : 0 ≤ S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) := by positivity
    have e5 : x * B₁ ^ m = 4 * C₄ ^ 2 * (S * K₁) * ((Mb ^ 2) ^ m * C₄ ^ m * 128 ^ m) := by
      have h6 : B₁ ^ m = (Mb ^ 2) ^ m * C₄ ^ m * 128 ^ m := by rw [hB₁, mul_pow (Mb ^ 2 * C₄) 128 m, mul_pow (Mb ^ 2) C₄ m]
      rw [h6, hx]
    have hstep : S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * (4 * 32 ^ (K + 1) * 4 ^ N) ≤ x * B₁ ^ m := by
      rw [e5, pow_add C₄ m 2]
      have hp : 0 ≤ 4 * C₄ ^ 2 * (S * K₁) * ((Mb ^ 2) ^ m * C₄ ^ m) := by positivity
      calc S * K₁ * (Mb ^ 2) ^ m * (C₄ ^ m * C₄ ^ 2) * (4 * 32 ^ (K + 1) * 4 ^ N)
          = 4 * C₄ ^ 2 * (S * K₁) * ((Mb ^ 2) ^ m * C₄ ^ m) * ((4 : ℝ) ^ N * 32 ^ (K + 1)) := by ring
        _ ≤ 4 * C₄ ^ 2 * (S * K₁) * ((Mb ^ 2) ^ m * C₄ ^ m) * 128 ^ m := by gcongr
        _ = _ := by ring
    have hstep2 : x * B₁ ^ m ≤ (B₁ * (1 + x)) ^ m := by
      rw [mul_pow B₁ (1 + x) m]
      have : x ≤ (1 + x) ^ m := by linarith
      have hBm : 0 ≤ B₁ ^ m := by positivity
      calc x * B₁ ^ m ≤ (1 + x) ^ m * B₁ ^ m := by gcongr
        _ = _ := by ring
    calc (1 / 2 : ℝ) ^ (K + 1) * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * (((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ)))
        ≤ 1 * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * (4 ^ N * (N : ℝ) ^ (2 * N)) * (4 * 32 ^ (K + 1) * (K.factorial : ℝ))) := by gcongr
      _ = (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * (4 * 32 ^ (K + 1) * 4 ^ N)) * ((N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by ring
      _ ≤ (B₁ * (1 + x)) ^ m * ((N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by
          gcongr
          exact hstep.trans hstep2
      _ = _ := by ring
  have hp : 0 ≤ T * X * FN := by positivity
  have eL : (ħ / 2) ^ (K + 1) * ((S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * (K + 1)).factorial : ℝ)
        * (α⁻¹) ^ (2 * (K + 1)) * X * FN) * t ^ (K + 1) / ((K + 1).factorial : ℝ))
      = ((ħ / 2) ^ (K + 1) * (α⁻¹ ^ (2 * (K + 1)) * t ^ (K + 1))) * X * FN * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * (((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ))) := by
    ring
  rw [eL, eT]
  unfold ddBound
  rw [← hm, ← hX, ← hT]
  calc (1 / 2) ^ (K + 1) * T * X * FN * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * (((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ)))
      = (T * X * FN) * ((1 / 2) ^ (K + 1) * (S * K₁ * (Mb ^ 2) ^ m * C₄ ^ (m + 2) * ((2 * N).factorial : ℝ) * (((2 + 2 * (K + 1)).factorial : ℝ) / ((K + 1).factorial : ℝ)))) := by ring
    _ ≤ (T * X * FN) * ((B₁ * (1 + x)) ^ m * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ)) := by gcongr
    _ = _ := by ring

section core

/-- **The Dyson remainder of Theorem 1.4R over `Γ'`, with weights based at `i`.** -/
theorem dd_core {β kp B C₁ : ℝ} (hβ : 1 / 2 < β) (hkp : 0 < kp) (hβ0 : 0 ≤ β) (hB0 : 0 ≤ B) (hB : FdbB β B) (hC : 0 ≤ C₁) (hF' : FCBound 1 C₁) :
    ∃ K₁ δ : ℝ, 0 ≤ K₁ ∧ 0 < δ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (W Wβ : SurfW Γ'),
      (∀ z, W.ω z = omG ((2 * β + 1) / 4) z) → (∀ z, Wβ.ω z = omG β z) →
      ∀ (ħ α t : ℝ) (K N : ℕ) (F : L2H') (hFd : F ∈ (expLambda α).domain), 0 < ħ → ħ ≤ 1 → 0 < α → α ≤ 1 → kp * ħ ≤ α ^ 3 → 0 ≤ t →
        t ≤ δ * Real.sqrt (α / ħ) →
        ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) (mulW hβ0 hB [] F))‖
          ≤ ddBound (((4 * mM C₁) ^ 2 * C4 (K3c 1 C₁) * 128) * (1 + 4 * C4 (K3c 1 C₁) ^ 2 * (Real.sqrt W.C.toReal * K₁))) α ħ t K N * ‖expLambda α ⟨F, hFd⟩‖ := by
  obtain ⟨K₁, δ, hK₁, hδ, h⟩ := vS_bound hβ hkp hβ0 hB0 hB hC hF'
  refine ⟨K₁, δ, hK₁, hδ, fun Γ' _ _ W Wβ hW hWβ ħ α t K N F hFd hħ hħ1 hα hα1 hk ht htδ => ?_⟩
  have hM1 : 1 ≤ 4 * mM C₁ := by have := one_le_mM C₁; linarith
  have hC₄1 : 1 ≤ C4 (K3c 1 C₁) := by
    unfold C4
    have := one_le_K3c 1 C₁
    nlinarith [sq_nonneg (K3c 1 C₁)]
  have hAi0 : 0 < α⁻¹ := inv_pos.2 hα
  have hC₄0 : 0 ≤ C4 (K3c 1 C₁) := by linarith
  have hS0 : 0 ≤ Real.sqrt W.C.toReal := Real.sqrt_nonneg _
  have hFN : 0 ≤ ‖expLambda α ⟨F, hFd⟩‖ := norm_nonneg _
  have hAh : 0 ≤ ((α * ħ)⁻¹) ^ (2 * N) := by positivity
  have hM0 : 0 ≤ Real.sqrt W.C.toReal * K₁ * ((4 * mM C₁) ^ 2) ^ (N + (K + 1)) * C4 (K3c 1 C₁) ^ (N + (K + 1) + 2) * ((2 * N).factorial : ℝ)
      * ((2 + 2 * (K + 1)).factorial : ℝ) * (α⁻¹) ^ (2 * (K + 1)) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ := by positivity
  have hb1 : ∀ ss : List ℝ, ss.length = K + 1 → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
      ‖W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) (mulW hβ0 hB [] F))‖
        ≤ Real.sqrt W.C.toReal * K₁ * ((4 * mM C₁) ^ 2) ^ (N + (K + 1)) * C4 (K3c 1 C₁) ^ (N + (K + 1) + 2) * ((2 * N).factorial : ℝ)
          * ((2 + 2 * (K + 1)).factorial : ℝ) * (α⁻¹) ^ (2 * (K + 1)) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ := fun ss hl hs => by
    have := h Γ' W Wβ hW hWβ ħ α t N ss F hFd hħ hħ1 hα hα1 hk ht htδ hs
    rwa [hl] at this
  have hD := SurfW.surf_D4_bound (W := W) (hb := ħ) (a := mulW hβ0 hB [] F) (K := K) (N := N) ht hM0 hb1
  exact hD.trans (dd_final hS0 hK₁ hM1 hC₄1 hħ hα ht hFN)

end core

section iso

variable (p : PGL(2, ℝ))

/-- `f ↦ f ∘ p` on `L²(ℍ)`. -/
noncomputable def isoL : L2H' →ₗᵢ[ℂ] L2H' := Lp.compMeasurePreservingₗᵢ ℂ (fun z => p • z) (measurePreserving_smul p (volume : Measure ℍ))

lemma isoL_ae (f : L2H') : ⇑(isoL p f) =ᵐ[volume] fun z => f (p • z) := Lp.coeFn_compMeasurePreserving f _

lemma isoL_inv (f : L2H') : isoL p (isoL p⁻¹ f) = f := by
  refine Lp.ext ?_
  have h := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp (isoL_ae p⁻¹ f)
  filter_upwards [isoL_ae p (isoL p⁻¹ f), h] with z h1 h2
  rw [h1]
  have h2' : (isoL p⁻¹ f : L2H') (p • z) = f (p⁻¹ • p • z) := h2
  rw [h2', inv_smul_smul]

/-- The unitary `f ↦ f ∘ p`. -/
noncomputable def isoU : L2H' ≃ₗᵢ[ℂ] L2H' := LinearIsometryEquiv.ofSurjective (isoL p) fun f => ⟨isoL p⁻¹ f, isoL_inv p f⟩

lemma isoU_ae (f : L2H') : ⇑(isoU p f) =ᵐ[volume] fun z => f (p • z) := isoL_ae p f

lemma isoU_toL2 (F : testFn) : isoU p (toL2 F) = toL2 (testP p F) := by
  refine Lp.ext ?_
  have h := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp (toL2_ae F)
  filter_upwards [isoU_ae p (toL2 F), h, toL2_ae (testP p F)] with z h1 h2 h3
  rw [h1, h3]
  have h2' : (toL2 F : L2H') (p • z) = (F : ℂ → ℂ) ((p • z : ℍ) : ℂ) := h2
  rw [h2']
  exact (tfn_testP p F z).symm

lemma isoU_symm_toL2 (F : testFn) : (isoU p).symm (toL2 F) = toL2 (testP p⁻¹ F) := by
  apply (isoU p).injective
  rw [LinearIsometryEquiv.apply_symm_apply, isoU_toL2]
  refine Lp.ext ?_
  filter_upwards [toL2_ae F, toL2_ae (testP p (testP p⁻¹ F))] with z h1 h2
  rw [h1, h2]
  have e := tfn_testP p (testP p⁻¹ F) z
  have e2 := tfn_testP p⁻¹ F (p • z)
  rw [inv_smul_smul] at e2
  exact (e.trans e2).symm

lemma intertwines_iso : IntertwinesOp negLap negLap (isoU p) where
  mem x hx := by
    obtain ⟨F, hF⟩ := toL2Equiv.surjective (⟨x, hx⟩ : negLap.domain)
    have hx' : x = toL2 F := by rw [← coe_toL2Equiv F, hF]
    rw [hx', isoU_toL2, ← coe_toL2Equiv]
    exact (toL2Equiv _).2
  comm x hx := by
    obtain ⟨F, rfl⟩ := toL2Equiv.surjective x
    have e : (⟨isoU p (toL2Equiv F : L2H'), hx⟩ : negLap.domain) = toL2Equiv (testP p F) :=
      Subtype.ext (by
        show isoU p ((toL2Equiv F : lapDomain) : L2H') = ((toL2Equiv (testP p F) : lapDomain) : L2H')
        rw [coe_toL2Equiv, coe_toL2Equiv, isoU_toL2])
    rw [e, negLap_toL2Equiv, negLap_toL2Equiv, map_neg, isoU_toL2, lapTest_testP]

lemma intertwines_iso_symm : IntertwinesOp negLap negLap (isoU p).symm where
  mem x hx := by
    obtain ⟨F, hF⟩ := toL2Equiv.surjective (⟨x, hx⟩ : negLap.domain)
    have hx' : x = toL2 F := by rw [← coe_toL2Equiv F, hF]
    rw [hx', isoU_symm_toL2, ← coe_toL2Equiv]
    exact (toL2Equiv _).2
  comm x hx := by
    obtain ⟨F, rfl⟩ := toL2Equiv.surjective x
    have e : (⟨(isoU p).symm (toL2Equiv F : L2H'), hx⟩ : negLap.domain) = toL2Equiv (testP p⁻¹ F) :=
      Subtype.ext (by
        show (isoU p).symm ((toL2Equiv F : lapDomain) : L2H') = ((toL2Equiv (testP p⁻¹ F) : lapDomain) : L2H')
        rw [coe_toL2Equiv, coe_toL2Equiv, isoU_symm_toL2])
    rw [e, negLap_toL2Equiv, negLap_toL2Equiv, map_neg, isoU_symm_toL2, lapTest_testP]

/-- `f ↦ f ∘ p` commutes with `-Δ`. -/
theorem negLapH_iso (u : L2H') (hu : u ∈ negLapH.domain) :
    ∃ h : isoU p u ∈ negLapH.domain, negLapH ⟨isoU p u, h⟩ = isoU p (negLapH ⟨u, hu⟩) :=
  friedrichsExt_U2 negLap negLap negLap_hasDenseDomain negLap_hasDenseDomain (intertwines_iso p) (intertwines_iso_symm p) ⟨u, hu⟩

/-- **The spectral distribution is invariant under isometries.** -/
theorem assoc_iso (u : L2H') : specE.assoc (isoU p u) = specE.assoc u := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hm : (fun x : ℝ => propFun 1 (-2 * t) x) = fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    funext x
    unfold propFun
    congr 1
    push_cast
    ring
  have key : ∀ v : L2H', charFun (specE.assoc v) t = ⟪v, evol negLapH_isSelfAdjoint 1 (-2 * t) v⟫_ℂ := fun v => by
    rw [charFun_apply_real, ← hm]
    exact (specE.inner_integral (propFun_mem 1 (-2 * t)) v).symm
  rw [key, key]
  have hS : ∀ (v : L2H') (hv : v ∈ negLapH.domain), ∃ h : ((isoU p : L2H' ≃ₗᵢ[ℂ] L2H') : L2H' →L[ℂ] L2H') v ∈ negLapH.domain,
      negLapH ⟨((isoU p : L2H' ≃ₗᵢ[ℂ] L2H') : L2H' →L[ℂ] L2H') v, h⟩ = ((isoU p : L2H' ≃ₗᵢ[ℂ] L2H') : L2H' →L[ℂ] L2H') (negLapH ⟨v, hv⟩) :=
    fun v hv => negLapH_iso p v hv
  have h := evol_intertwine negLapH_isSelfAdjoint negLapH_isSelfAdjoint _ hS 1 (-2 * t) u
  have h' : isoU p (evol negLapH_isSelfAdjoint 1 (-2 * t) u) = evol negLapH_isSelfAdjoint 1 (-2 * t) (isoU p u) := h
  rw [← h', LinearIsometryEquiv.inner_map_map]

/-- **`‖e^{αΛ} (f ∘ p)‖ = ‖e^{αΛ} f‖`.** -/
theorem expLambda_iso {α : ℝ} {u : L2H'} (hu : u ∈ (expLambda α).domain) :
    ∃ h : isoU p u ∈ (expLambda α).domain, ‖expLambda α ⟨isoU p u, h⟩‖ = ‖expLambda α ⟨u, hu⟩‖ := by
  set f : ℝ → ℂ := fun s => ((Real.exp (α * Real.sqrt s) : ℝ) : ℂ) with hf
  have hfm : Measurable f :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have h1 : u ∈ integralDomain (spectralMeasure negLapH_isSelfAdjoint) f := by
    have h0 : u ∈ (functionalCalculus negLapH_isSelfAdjoint f).domain := hu
    rwa [functionalCalculus_domain] at h0
  have h2 : isoU p u ∈ integralDomain (spectralMeasure negLapH_isSelfAdjoint) f := by
    rw [mem_integralDomain] at h1 ⊢
    have e : (spectralMeasure negLapH_isSelfAdjoint).assoc (isoU p u) = (spectralMeasure negLapH_isSelfAdjoint).assoc u := assoc_iso p u
    rw [e]
    exact h1
  have h3 : isoU p u ∈ (expLambda α).domain := by
    have : isoU p u ∈ (functionalCalculus negLapH_isSelfAdjoint f).domain := by
      rw [functionalCalculus_domain]; exact h2
    exact this
  refine ⟨h3, ?_⟩
  have n1 := norm_sq_pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) hfm ⟨u, h1⟩
  have n2 := norm_sq_pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) hfm ⟨isoU p u, h2⟩
  have e1 : ‖expLambda α ⟨u, hu⟩‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂((spectralMeasure negLapH_isSelfAdjoint).assoc u) := n1
  have e2 : ‖expLambda α ⟨isoU p u, h3⟩‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂((spectralMeasure negLapH_isSelfAdjoint).assoc (isoU p u)) := n2
  have e3 : (spectralMeasure negLapH_isSelfAdjoint).assoc (isoU p u) = (spectralMeasure negLapH_isSelfAdjoint).assoc u := assoc_iso p u
  rw [e3, ← e1] at e2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e2

end iso

end Qschubert
