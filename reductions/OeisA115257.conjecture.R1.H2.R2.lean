import OMAReductions.R_OeisA115257_conjecture_R1
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# Degree restrictions from the initial Newton edge

The weighted Gauss norm gives a necessary factor-degree condition at any prime.
At 2 the coefficient valuations make this explicit for truncations near powers
of two, and for one above a power of two only the half-power degree remains.
-/

namespace OMA.R_OeisA115257_conjecture_R1_H2_R2


open Polynomial OeisA115257
open scoped BigOperators

/-- The factor degrees remaining just above a power of two. -/
def H1 : Prop :=
  ∀ r n : ℕ, 1 ≤ r → 2^(r+1) < n → n ≤ 3*2^r →
    ∀ g : Polynomial ℚ, g.Monic → 2 ≤ g.natDegree →
      g.natDegree ≤ n / 2 → (g.natDegree ≤ n - 2^(r+1) ∨ 2^r ≤ g.natDegree) →
      ¬ g ∣ polyQ n

/-- The other indices, restricted by the initial Newton edges over every prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (¬ ∃ r : ℕ, n = 2^r) →
    (¬ ∃ r : ℕ, 1 ≤ r ∧ 2^(r+1) < n ∧ n ≤ 3*2^r) →
    ∀ g : Polynomial ℚ, g.Monic → 2 ≤ g.natDegree →
      g.natDegree ≤ n / 2 →
      (∀ p s t m : ℕ, p.Prime → 0 < s → s.Coprime t →
        (∀ i : ℕ, padicNorm p ((polyQ n).coeff i)^s * (p : ℚ)^(t*i) ≤ 1) →
        padicNorm p ((polyQ n).coeff m)^s * (p : ℚ)^(t*m) = 1 →
        g.natDegree < s → m + g.natDegree ≤ n) →
      ¬ g ∣ polyQ n

section

private theorem exists_weight (p s : ℕ) (hs : 0 < s) [Fact p.Prime] :
    ∃ V : AbsoluteValue ℚ ℝ, (∀ x : ℚ, V x = (padicNorm p x : ℝ)^s) ∧
      IsNonarchimedean V := by
  let V : AbsoluteValue ℚ ℝ := {
    toFun x := ((padicNorm p x : ℚ) : ℝ) ^ s
    map_mul' x y := by rw [padicNorm.mul, Rat.cast_mul, mul_pow]
    nonneg' x := pow_nonneg (by exact_mod_cast padicNorm.nonneg x) _
    eq_zero' x := by
      rw [pow_eq_zero_iff hs.ne', Rat.cast_eq_zero]
      exact ⟨padicNorm.zero_of_padicNorm_eq_zero, fun h => by subst x; exact padicNorm.zero⟩
    add_le' x y := by
      have h : ((padicNorm p (x + y) : ℚ) : ℝ) ≤
          max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ) := by
        exact_mod_cast padicNorm.nonarchimedean (p := p) (q := x) (r := y)
      calc
        _ ≤ (max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ)) ^ s :=
          pow_le_pow_left₀ (by exact_mod_cast padicNorm.nonneg (p := p) (x + y)) h _
        _ ≤ _ := by
          rcases le_total (padicNorm p x) (padicNorm p y) with hxy | hyx
          · rw [max_eq_right (by exact_mod_cast hxy)]
            apply le_add_of_nonneg_left
            exact pow_nonneg (by exact_mod_cast padicNorm.nonneg (p := p) x) _
          · rw [max_eq_left (by exact_mod_cast hyx)]
            apply le_add_of_nonneg_right
            exact pow_nonneg (by exact_mod_cast padicNorm.nonneg (p := p) y) _ }
  refine ⟨V, fun _ => rfl, ?_⟩
  intro x y
  have h : ((padicNorm p (x + y) : ℚ) : ℝ) ≤
      max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ) := by
    exact_mod_cast padicNorm.nonarchimedean (p := p) (q := x) (r := y)
  have hw := pow_le_pow_left₀
    (show (0 : ℝ) ≤ (padicNorm p (x + y) : ℚ) by exact_mod_cast padicNorm.nonneg _) h s
  change ((padicNorm p (x+y) : ℚ) : ℝ)^s ≤
    max (((padicNorm p x : ℚ) : ℝ)^s) (((padicNorm p y : ℚ) : ℝ)^s)
  rcases le_total (padicNorm p x) (padicNorm p y) with hxy | hyx
  · rw [max_eq_right (by exact_mod_cast hxy)] at hw
    exact hw.trans (le_max_right _ _)
  · rw [max_eq_left (by exact_mod_cast hyx)] at hw
    exact hw.trans (le_max_left _ _)

private theorem normalized_eq_index {p s t i : ℕ} (hp : p.Prime) (hs : 0 < s)
    (hst : s.Coprime t) {a : ℚ} (h : padicNorm p a ^ s * (p : ℚ)^(t*i) = 1) : s ∣ i := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp [hs.ne'] at h
  have hp1 : 1 < (p : ℚ) := by exact_mod_cast hp.one_lt
  rw [padicNorm.eq_zpow_of_nonzero ha, ← zpow_natCast, ← zpow_mul,
    ← zpow_natCast, ← zpow_add₀ (by positivity : (p : ℚ) ≠ 0), ← zpow_zero (p : ℚ)] at h
  have e : -padicValRat p a * (s : ℤ) + ((t*i : ℕ) : ℤ) = 0 :=
    (zpow_right_injective₀ (zero_lt_one.trans hp1) hp1.ne') h
  have he : ((t*i : ℕ) : ℤ) = (s : ℤ) * padicValRat p a := by
    linarith only [e, mul_comm (s : ℤ) (padicValRat p a)]
  exact hst.dvd_of_dvd_mul_left (Int.natCast_dvd_natCast.mp ⟨_, he⟩)

/-- A rational factor of degree below the slope denominator leaves room for the given edge index in the complementary factor. -/
theorem edge_degree {p s t m : ℕ} (hp : p.Prime) (hs : 0 < s) (hst : s.Coprime t)
    {F G : Polynomial ℚ} (hF0 : F.coeff 0 = 1)
    (hbound : ∀ i : ℕ, padicNorm p (F.coeff i)^s * (p : ℚ)^(t*i) ≤ 1)
    (hface : padicNorm p (F.coeff m)^s * (p : ℚ)^(t*m) = 1)
    (hdiv : G ∣ F) (hsmall : G.natDegree < s) :
    m + G.natDegree ≤ F.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, hV, hna⟩ := exists_weight p s hs
  let r : ℝ := (p : ℝ)^t
  have hr : 0 < r := pow_pos (by exact_mod_cast hp.pos) _
  obtain ⟨H, hprod⟩ := hdiv
  have hg0 : G.coeff 0 ≠ 0 := by
    intro h
    rw [hprod, mul_coeff_zero, h, zero_mul] at hF0
    norm_num at hF0
  let U := C (G.coeff 0)⁻¹ * G
  let W := C (G.coeff 0) * H
  have hU0 : U.coeff 0 = 1 := by simp [U, hg0]
  have hP : U * W = F := by
    rw [hprod]
    unfold U W
    calc
      _ = (C (G.coeff 0)⁻¹ * C (G.coeff 0)) * (G * H) := by ring
      _ = _ := by rw [← C_mul, inv_mul_cancel₀ hg0, C_1, one_mul]
  have hW0 : W.coeff 0 = 1 := by
    have h := congrArg (fun P : Polynomial ℚ => P.coeff 0) hP
    simpa only [mul_coeff_zero, hU0, one_mul, hF0] using h
  have hF : F.gaussNorm V r ≤ 1 := by
    obtain ⟨i, hi⟩ := F.exists_eq_gaussNorm V r
    rw [hi]
    rw [hV]
    change (padicNorm p (F.coeff i) : ℝ)^s * ((p : ℝ)^t)^i ≤ 1
    rw [← pow_mul]
    exact_mod_cast hbound i
  have hU : 1 ≤ U.gaussNorm V r := by
    have h := U.le_gaussNorm V hr.le 0
    rw [hU0] at h
    simpa [hV] using h
  have hW : 1 ≤ W.gaussNorm V r := by
    have h := W.le_gaussNorm V hr.le 0
    rw [hW0] at h
    simpa [hV] using h
  rw [← hP, Polynomial.gaussNorm_mul (v := V) (c := r) hna hr] at hF
  have huBound : ∀ i, V (U.coeff i) * r ^ i ≤ 1 := fun i =>
    (U.le_gaussNorm V hr.le i).trans (by nlinarith)
  have hwBound : ∀ i, V (W.coeff i) * r ^ i ≤ 1 := fun i =>
    (W.le_gaussNorm V hr.le i).trans (by nlinarith)
  have hUd : U.natDegree = G.natDegree := natDegree_C_mul (inv_ne_zero hg0)
  have hsum : U.natDegree + W.natDegree = F.natDegree :=
    (natDegree_mul (by intro h; simp [h] at hU0) (by intro h; simp [h] at hW0)).symm.trans
      (congrArg natDegree hP)
  by_contra! hn
  have hnW : W.natDegree < m := by omega
  have hlt (i j : ℕ) (hij : i+j=m) :
      V (U.coeff i * W.coeff j) * r ^ m < 1 := by
    rw [← hij, pow_add, map_mul]
    calc
      _ = (V (U.coeff i) * r^i) * (V (W.coeff j) * r^j) := by ring
      _ < 1 := by
        by_cases hi : i = 0
        · subst i
          simp only [zero_add] at hij
          subst j
          rw [coeff_eq_zero_of_natDegree_lt hnW, map_zero, zero_mul, mul_zero]
          norm_num
        · have hstrict : V (U.coeff i) * r^i < 1 := by
            apply lt_of_le_of_ne (huBound i)
            intro he
            have hiU : i ≤ U.natDegree := by
              by_contra! hh
              rw [coeff_eq_zero_of_natDegree_lt hh, map_zero, zero_mul] at he
              norm_num at he
            have hie : padicNorm p (U.coeff i)^s * (p : ℚ)^(t*i) = 1 := by
              rw [hV] at he
              change (padicNorm p (U.coeff i) : ℝ)^s * ((p : ℝ)^t)^i = 1 at he
              rw [← pow_mul] at he
              exact_mod_cast he
            exact (not_le_of_gt (hiU.trans_lt (hUd ▸ hsmall)))
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) (normalized_eq_index hp hs hst hie))
          have hnn : 0 ≤ V (U.coeff i) * r^i := mul_nonneg (apply_nonneg _ _) (pow_nonneg hr.le _)
          calc
            _ ≤ (V (U.coeff i) * r^i) * 1 := mul_le_mul_of_nonneg_left (hwBound j) hnn
            _ < _ := by rwa [mul_one]
  have hface' : V (F.coeff m) * r^m = 1 := by
    rw [hV]
    change (padicNorm p (F.coeff m) : ℝ)^s * ((p : ℝ)^t)^m = 1
    rw [← pow_mul]
    exact_mod_cast hface
  rw [← hP, coeff_mul] at hface'
  have hm : (Finset.HasAntidiagonal.antidiagonal m).Nonempty := ⟨(0,m), by simp⟩
  have hsup := IsNonarchimedean.apply_sum_le_sup hna hm
    (l := fun ij : ℕ × ℕ => U.coeff ij.1 * W.coeff ij.2)
  obtain ⟨ij, hij, hmax⟩ := Finset.exists_mem_eq_sup' hm
    (fun ij : ℕ × ℕ => V (U.coeff ij.1 * W.coeff ij.2))
  rw [hmax] at hsup
  exact (ne_of_lt ((mul_le_mul_of_nonneg_right hsup (pow_nonneg hr.le m)).trans_lt
    (hlt ij.1 ij.2 ((by simpa using hij))))) hface'

open OMA.R_OeisA115257_conjecture_R1
open OMA.R_OeisA115257_conjecture_R1.A115257Power
open OMA.R_OeisA115257_conjecture_R1.A115257Valuation

private theorem norm_coeff_of_le {n i s : ℕ} (hin : i ≤ n) :
    padicNorm 2 ((polyQ n).coeff i)^s * (2 : ℚ)^i =
      (2 : ℚ)^((i : ℤ) - (s : ℤ) * ↑((Nat.centralBinom i ^ 2 / (i+1)).factorization 2)) := by
  have hpos : 0 < Nat.centralBinom i ^ 2 / (i+1) := aN_pos true i
  have hcoeff : (polyQ n).coeff i = ((Nat.centralBinom i ^ 2 / (i+1) : ℕ) : ℚ) := by
    have h := coeff_family true n i
    simp only [if_true, if_pos hin] at h
    exact h.trans (aN_cast true i).symm
  rw [hcoeff, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hpos.ne'),
    padicValRat.of_nat, ← Nat.factorization_def _ Nat.prime_two, ← zpow_natCast,
    ← zpow_mul, ← zpow_natCast]
  push_cast
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  ring

private theorem val_at_least_three {r k : ℕ} (hr : 1 ≤ r)
    (h₁ : 2^(r+1) < k) (h₂ : k < 2^(r+1+1)) :
    3 ≤ (Nat.centralBinom k ^ 2 / (k+1)).factorization 2 := by
  have h := aN_val true k
  change (Nat.centralBinom k ^ 2 / (k+1)).factorization 2 =
    2 * (Nat.centralBinom k).factorization 2 - (k+1).factorization 2 at h
  have hc := central_val_between (r+1) k h₁ h₂
  have hk5 : 5 ≤ k :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 2 ≤ r+1 by omega)).trans_lt h₁
  have hv := (Nat.factorization_le_iff_dvd (by omega : k+1 ≠ 0)
    (Nat.centralBinom_ne_zero k)).mpr (Nat.succ_dvd_centralBinom k) 2
  rw [h]
  by_cases he : 2 ∣ k
  · rw [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬2 ∣ k+1)]
    omega
  · by_cases hc3 : 3 ≤ (Nat.centralBinom k).factorization 2
    · omega
    · have hs2 : (Nat.digits 2 k).sum = 2 := by
        rw [central_val k] at hc hc3
        omega
      rw [Nat.digits_def' (by decide) (by omega : 0 < k), List.sum_cons,
        show k%2=1 by omega] at hs2
      obtain ⟨j, hj⟩ := (digit_sum_eq_one_iff (k/2)).mp (by omega)
      have hj1 : 1 ≤ j := by
        by_contra! h
        have h0 : j = 0 := by omega
        rw [h0, pow_zero] at hj
        omega
      have he2 : 2 ∣ k / 2 := hj.symm ▸ even_pow2 j hj1
      have hk1 : k+1 = 2*(k/2+1) := by omega
      rw [hk1, Nat.factorization_mul (by decide) (by omega), Finsupp.add_apply,
        Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by omega : ¬2 ∣ k/2+1)]
      omega

private theorem q_degree (n : ℕ) : (polyQ n).natDegree = n := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have h := coeff_family true n i
    simpa only [if_true, if_neg (not_le.mpr hi)] using h
  · exact le_natDegree_of_ne_zero (coeff_top true n)

/-- For truncations shortly above a power of two, factor degrees between
the excess degree and half that power are excluded. -/
theorem near_power_factor_degree {r n : ℕ} (hr : 1 ≤ r)
    (hlo : 2^(r+1) ≤ n) (hhi : n ≤ 3*2^r) {g : Polynomial ℚ}
    (hg : g ∣ polyQ n) :
    g.natDegree ≤ n - 2^(r+1) ∨ 2^r ≤ g.natDegree := by
  let s : ℕ := 2^r
  let m : ℕ := 2^(r+1)
  have hms : m = 2*s := by simp [m, s, pow_succ']
  have hs : 0 < s := by positivity
  change m ≤ n at hlo
  change n ≤ 3*s at hhi
  change g.natDegree ≤ n - m ∨ s ≤ g.natDegree
  by_cases hsmall : g.natDegree < s
  · left
    have h0 : (polyQ n).coeff 0 = 1 := by
      have h := coeff_family true n 0
      simpa [Nat.centralBinom] using h
    have hface : padicNorm 2 ((polyQ n).coeff m)^s * (2 : ℚ)^m = 1 := by
      rw [norm_coeff_of_le hlo]
      have hv := pow2_aN_val true (r+1) (by omega)
      change (Nat.centralBinom m ^ 2 / (m+1)).factorization 2 = 2 at hv
      rw [hv]
      have e : (m : ℤ) - (s : ℤ) * (↑(2 : ℕ) : ℤ) = 0 := by omega
      rw [e, zpow_zero]
    have hbound (i : ℕ) : padicNorm 2 ((polyQ n).coeff i)^s * (2 : ℚ)^i ≤ 1 := by
      by_cases hi : i ≤ n
      · rw [norm_coeff_of_le hi, ← zpow_zero (2 : ℚ), zpow_le_zpow_iff_right₀ (by norm_num)]
        have hval : i ≤ s * (Nat.centralBinom i ^ 2 / (i+1)).factorization 2 := by
          by_cases hi' : i ≤ m
          · rcases i with _ | _ | i
            · simp
            · have h1 : (Nat.centralBinom 1 ^ 2 / (1+1)).factorization 2 = 1 := by
                have h : Nat.centralBinom 1 ^ 2 / (1+1) = 2 := by decide
                rw [h, Nat.prime_two.factorization_self]
              simpa [h1] using (show 1 ≤ s by omega)
            · have h4 := aN_four_dvd_Q (i+2) (by omega)
              change 2^2 ∣ Nat.centralBinom (i+2)^2 / (i+2+1) at h4
              have hpos : 0 < Nat.centralBinom (i+2)^2 / (i+2+1) := aN_pos true (i+2)
              have hv := (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp h4
              exact hi'.trans (by rw [hms, mul_comm 2]; exact Nat.mul_le_mul_left s hv)
          · have upper : i < 2^(r+1+1) := by
              rw [pow_succ', ← show m = 2^(r+1) by rfl]
              omega
            have hmid : m < i := lt_of_not_ge hi'
            have hv := val_at_least_three (r := r) hr hmid upper
            exact (hi.trans hhi).trans (by rw [mul_comm 3]; exact Nat.mul_le_mul_left s hv)
        exact sub_nonpos.mpr (by exact_mod_cast hval)
      · have hz := coeff_eq_zero_of_natDegree_lt (show (polyQ n).natDegree < i by
            rw [q_degree]; exact lt_of_not_ge hi)
        simp [hz, hs.ne']
    have he := edge_degree (t := 1) Nat.prime_two hs (Nat.coprime_one_right _) h0
      (fun i => by simpa using hbound i) (by simpa using hface) hg hsmall
    rw [q_degree] at he
    omega
  · exact Or.inr (le_of_not_gt hsmall)

end

theorem main : H1 → H2 → OMA.R_OeisA115257_conjecture_R1.H2 := by
  intro h₁ h₂ n hn hnPow g hg hd hlo hdiv
  rw [q_degree] at hlo
  by_cases hnear : ∃ r : ℕ, 1 ≤ r ∧ 2^(r+1) < n ∧ n ≤ 3*2^r
  · obtain ⟨r, hr, hlt, hhi⟩ := hnear
    exact h₁ r n hr hlt hhi g hg hd hlo (near_power_factor_degree hr hlt.le hhi hdiv) hdiv
  · apply h₂ n hn hnPow hnear g hg hd hlo _ hdiv
    intro p s t m hp hs hst hbound hface hsmall
    have hz : (polyQ n).coeff 0 = 1 := by
      have h := OMA.R_OeisA115257_conjecture_R1.coeff_family true n 0
      simpa [Nat.centralBinom] using h
    simpa only [q_degree] using edge_degree hp hs hst hz hbound hface hdiv hsmall

end OMA.R_OeisA115257_conjecture_R1_H2_R2
