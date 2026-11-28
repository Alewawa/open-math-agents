import OMAReductions.R_OeisA115257_conjecture_R1
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Restrictions on the degrees of factors of the squared-binomial truncations. -/

open Polynomial OeisA115257
open OMA.R_OeisA115257_conjecture_R1

namespace OMA.R_OeisA115257_conjecture_R1_H1_R1

private theorem low_coeff_even_of_factorization {F A B W : ℤ[X]} {n j : ℕ}
    (hA : A.Monic) (hB : B.Monic) (hdeg : F.natDegree = n) (hprod : F = A * B)
    (hF : F = X ^ n + C 4 * W)
    (hj : j < A.natDegree) (hgap : j < B.natDegree - A.natDegree) :
    (2 : ℤ) ∣ W.coeff j := by
  let red := Polynomial.mapRingHom (Int.castRingHom (ZMod 2))
  have hABdeg : A.natDegree + B.natDegree = n := by rw [← hA.natDegree_mul hB, ← hprod, hdeg]
  have hle : A.natDegree ≤ B.natDegree := by omega
  have htwo : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hfour : (4 : (ZMod 2)[X]) = 0 := by rw [show (4 : (ZMod 2)[X]) = 2 * 2 by norm_num, htwo, zero_mul]
  have hred : red (A * B) = X ^ n := by
    rw [← hprod, hF]
    simp [red, hfour]
  obtain ⟨hrA, hrB⟩ := BinomialPowerTwo.red_eq_X_pow_of_mul hA hB hred
  obtain ⟨U, hU⟩ := BinomialPowerTwo.eq_pow_add_two hrA
  obtain ⟨V, hV⟩ := BinomialPowerTwo.eq_pow_add_two hrB
  have htop : (X : ℤ[X]) ^ A.natDegree * X ^ B.natDegree = X ^ n := by rw [← pow_add, hABdeg]
  have hident : X ^ A.natDegree * V + X ^ B.natDegree * U + C 2 * (U * V) = C 2 * W := by
    have he := hprod.symm.trans hF
    rw [hU, hV, show C (4 : ℤ) = C 2 * C 2 by rw [← C_mul]; norm_num] at he
    have he' : C (2 : ℤ) * (X ^ A.natDegree * V + X ^ B.natDegree * U + C 2 * (U * V)) =
        C 2 * (C 2 * W) := by linear_combination he - htop
    exact mul_left_cancel₀ (by norm_num) he'
  have hz : (X : (ZMod 2)[X]) ^ A.natDegree * red V + X ^ B.natDegree * red U = 0 := by
    have he := congrArg red hident
    simpa [red, htwo] using he
  have hshift : red V = X ^ (B.natDegree - A.natDegree) * red U := by
    have hx : (X : (ZMod 2)[X]) ^ B.natDegree = X ^ A.natDegree * X ^ (B.natDegree - A.natDegree) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [hx, mul_assoc, ← mul_add] at hz
    have hsum := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ X_ne_zero)
    linear_combination hsum - (X ^ (B.natDegree - A.natDegree) * red U) * htwo
  have hcoeff : (U * V).coeff j = W.coeff j := by
    have he := congrArg (fun P : ℤ[X] => P.coeff j) hident
    simp [coeff_X_pow_mul', coeff_add, show ¬ A.natDegree ≤ j by omega,
      show ¬ B.natDegree ≤ j by omega] at he
    omega
  have hUV : (red (U * V)).coeff j = 0 := by
    rw [map_mul, hshift, mul_left_comm, coeff_X_pow_mul', if_neg (by omega)]
  have hzW : (W.coeff j : ZMod 2) = 0 := by
    change ((U * V).map (Int.castRingHom (ZMod 2))).coeff j = 0 at hUV
    rwa [coeff_map, hcoeff] at hUV
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzW



private theorem reciprocal_monic (n : ℕ) : ((∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i)).Monic := by
  exact A115257Lift.monic_revInt (fun k => (Nat.centralBinom k : ℤ) ^ 2) n (by decide)

private theorem reciprocal_natDegree (n : ℕ) : ((∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i)).natDegree = n := by
  exact A115257Lift.natDegree_revInt (fun k => (Nat.centralBinom k : ℤ) ^ 2) n (by decide)

private theorem reciprocal_map (n : ℕ) : ((∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i)).map (Int.castRingHom ℚ) = (polyP n).reverse := by
  have h : (Nat.centralBinom n : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Nat.centralBinom_ne_zero n)
  simpa [polyP] using (A115257Lift.reverse_trunc_eq (fun k => (Nat.centralBinom k : ℤ) ^ 2) n h).symm

private theorem reciprocal_factor_degree_gap (r n : ℕ) (hpow : 2 ^ r ≤ n)
    {A B : ℤ[X]} (hA : A.Monic) (hB : B.Monic) (hprod : (∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i) = A * B)
    (hdleft : n - 2 ^ r < A.natDegree) (hdright : 2 * A.natDegree < 2 ^ r) : False := by
  obtain ⟨W, hW⟩ := A115257Power.fP_form n
  have hF : (∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i) = X ^ n + C 4 * W := by simpa using hW
  have hd : A.natDegree + B.natDegree = n := by rw [← hA.natDegree_mul hB, ← hprod, reciprocal_natDegree]
  have hw2 := low_coeff_even_of_factorization hA hB (reciprocal_natDegree n) hprod hF hdleft (by omega)
  have hj : n - 2 ^ r < n := Nat.sub_lt (lt_of_lt_of_le (by positivity) hpow) (by positivity)
  have hw := A115257Power.fP_Wcoeff hj W hW
  rw [show n - (n - 2 ^ r) = 2 ^ r by omega] at hw
  have hcv := A115257Valuation.central_val_pow r
  have hcn := Nat.centralBinom_ne_zero (2 ^ r)
  have hnot : ¬ (2 : ℕ) ^ 3 ∣ (Nat.centralBinom (2 ^ r)) ^ 2 := by
    rw [Nat.prime_two.pow_dvd_iff_le_factorization (pow_ne_zero 2 hcn)]
    simp [Nat.factorization_pow, Finsupp.smul_apply, hcv]
  apply hnot
  have hdvd : (8 : ℤ) ∣ (Nat.centralBinom (2 ^ r) : ℤ) ^ 2 := by
    obtain ⟨w, hw'⟩ := hw2
    have hh : (Nat.centralBinom (2 ^ r) : ℤ) ^ 2 = 4 * W.coeff (n - 2 ^ r) := by simpa using hw
    exact ⟨w, by rw [hh, hw']; ring⟩
  exact_mod_cast hdvd

theorem polyP_factor_degree_gap (r n : ℕ) (hpow : 2 ^ r ≤ n) {g : ℚ[X]}
    (hdleft : n - 2 ^ r < g.natDegree) (hdright : 2 * g.natDegree < 2 ^ r) : ¬ g ∣ polyP n := by
  rintro ⟨f, hgf⟩
  have hp0 : (polyP n).coeff 0 = 1 := by
    simpa [Nat.centralBinom] using coeff_family false n 0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro hz
    rw [hgf, mul_coeff_zero, hz, zero_mul] at hp0
    norm_num at hp0
  let F : ℤ[X] := ∑ i ∈ Finset.range (n + 1), C ((Nat.centralBinom (n - i) : ℤ) ^ 2) * X ^ i
  have hFm : F.Monic := reciprocal_monic n
  have hFmap : F.map (algebraMap ℤ ℚ) = (polyP n).reverse := reciprocal_map n
  have hdiv : g.reverse ∣ F.map (algebraMap ℤ ℚ) := by
    rw [hFmap, hgf, reverse_mul_of_domain]
    exact dvd_mul_right _ _
  have hgr0 : g.reverse ≠ 0 := fun h => hg0 (by rw [reverse_eq_zero.mp h, coeff_zero])
  have hc : g.reverse.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgr0
  obtain ⟨A, hA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hFm hdiv
  have hAmap : A.map (algebraMap ℤ ℚ) = g.reverse * C g.reverse.leadingCoeff⁻¹ := by
    calc
      _ = (A.map (algebraMap ℤ ℚ) * C g.reverse.leadingCoeff) * C g.reverse.leadingCoeff⁻¹ := by
        rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, mul_one]
      _ = _ := by rw [hA]
  have hAm : A.Monic := ((IsFractionRing.injective ℤ ℚ).monic_map_iff).mpr
    (hAmap ▸ monic_mul_leadingCoeff_inv hgr0)
  have hdivMap : A.map (algebraMap ℤ ℚ) ∣ F.map (algebraMap ℤ ℚ) := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hAmap]
    refine ⟨C g.reverse.leadingCoeff * Q, ?_⟩
    rw [← mul_assoc, mul_assoc g.reverse, ← C_mul, inv_mul_cancel₀ hc, C_1, mul_one, hQ]
  have hzero : (F %ₘ A).map (algebraMap ℤ ℚ) = 0 := by
    rw [map_modByMonic _ hAm, modByMonic_eq_zero_iff_dvd (hAm.map _)]
    exact hdivMap
  have hdvd : A ∣ F := (modByMonic_eq_zero_iff_dvd hAm).mp
    ((Polynomial.map_eq_zero_iff (IsFractionRing.injective ℤ ℚ)).mp hzero)
  obtain ⟨B, hAB⟩ := hdvd
  have hBm : B.Monic := hAm.of_mul_monic_left (hAB ▸ hFm)
  have hdeg : A.natDegree = g.natDegree := by
    rw [← hAm.natDegree_map (algebraMap ℤ ℚ), hAmap,
      natDegree_mul_C (inv_ne_zero hc), reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hg0),
      Nat.sub_zero]
  exact reciprocal_factor_degree_gap r n hpow hAm hBm hAB (by rwa [hdeg]) (by rwa [hdeg])

private theorem even_index_real_pos (n : ℕ) (x : ℝ) :
    0 < ((polyP (2 * n)).map (algebraMap ℚ ℝ)).eval x := by
  let a (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) ^ 2
  let r (k : ℕ) : ℝ := ((4 : ℝ) - 2 / ((k : ℝ) + 1)) ^ 2
  have ha (k : ℕ) : 0 ≤ a k := sq_nonneg _
  have hr (k : ℕ) : a (k + 1) = r k * a k := by
    have h : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hn : (k : ℝ) + 1 ≠ 0 := by positivity
    have h' : (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) / ((k : ℝ) + 1) :=
      (eq_div_iff hn).mpr (by linarith only [h])
    dsimp only [a, r]
    rw [h']
    field_simp
    ring
  have hrmono (k : ℕ) : r k ≤ r (k + 1) := by
    dsimp only [r]
    push_cast
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
      (show (2 : ℝ) ≤ 4 * ((k : ℝ) + 1) by nlinarith [show (0 : ℝ) ≤ k by positivity])
    have h2 : (2 : ℝ) / ((k : ℝ) + 1 + 1) ≤ 2 / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    gcongr
  have htriple (k : ℕ) : 0 ≤ a k + 2 * a (k + 1) * x + a (k + 2) * x ^ 2 := by
    have h : 0 ≤ a k * (1 + r k * x) ^ 2 +
        ((r (k + 1) - r k) * a (k + 1)) * x ^ 2 :=
      add_nonneg (mul_nonneg (ha k) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr (hrmono k)) (ha _)) (sq_nonneg _))
    rw [hr (k + 1), hr k]
    rw [hr k] at h
    linarith only [h]
  have hlower (j : ℕ) : 1 + a (2 * j) * x ^ (2 * j) ≤
      2 * ∑ k ∈ Finset.range (2 * j + 1), a k * x ^ k := by
    induction j with
    | zero => norm_num [a, Nat.centralBinom]
    | succ j ih =>
      rw [Nat.mul_succ, show 2*j + 2 + 1 = (2*j+1) + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have hx : 0 ≤ x ^ (2 * j) := by rw [pow_mul]; positivity
      have h := mul_nonneg hx (htriple (2 * j))
      rw [show 2*j+1+1 = 2*j+2 by omega]
      simp only [pow_add, pow_one]
      linarith only [ih, h]
  have hv : ((polyP (2 * n)).map (algebraMap ℚ ℝ)).eval x =
      ∑ k ∈ Finset.range (2 * n + 1), a k * x ^ k := by simp [polyP, a]
  rw [hv]
  have hx : 0 ≤ x ^ (2 * n) := by rw [pow_mul]; positivity
  linarith [hlower n, mul_nonneg (ha (2 * n)) hx]

theorem even_index_factor_degree (n : ℕ) {g : ℚ[X]} (hg : g ∣ polyP (2 * n)) : Even g.natDegree := by
  have real_even (P : ℝ[X]) : (∀ x : ℝ, P.eval x ≠ 0) → Even P.natDegree := by
    induction P using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit u hu => simp [natDegree_eq_zero_of_isUnit hu]
    | mul a i ha hi ih =>
      intro h
      have ha' := ih (fun x hx => h x (by simp [hx]))
      have h1 : i.natDegree ≠ 1 := by
        intro hdeg
        obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one
          (show i.degree = 1 by rw [degree_eq_natDegree hi.ne_zero, hdeg]; rfl)
        exact h x (by simp [IsRoot.def.mp hx])
      have h2 := hi.natDegree_le_two
      have he : Even i.natDegree := by
        rcases (show i.natDegree = 0 ∨ i.natDegree = 2 by omega) with h₀ | h₂
        · simp [h₀]
        · simp [h₂]
      rw [natDegree_mul hi.ne_zero ha]
      exact he.add ha'
  obtain ⟨f, hf⟩ := hg
  have h := real_even (g.map (algebraMap ℚ ℝ)) (by
    intro x hx
    have hp := even_index_real_pos n x
    rw [hf, Polynomial.map_mul, Polynomial.eval_mul, hx, zero_mul] at hp
    exact (lt_irrefl _ hp))
  simpa using h

/-- The quadratic case. -/
def H1 : Prop := ∀ n : ℕ, 3 ≤ n → ∀ g : ℚ[X],
  g.Monic → g.natDegree = 2 → ¬ g ∣ polyP n

/-- The possible even degrees larger than two, after the mod-four restriction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (¬ ∃ r : ℕ, n = 2 ^ r) →
  ∀ g : ℚ[X], g.Monic → 4 ≤ g.natDegree → g.natDegree ≤ (polyP n).natDegree / 2 →
    Even g.natDegree → (∀ r : ℕ, 2 ^ r ≤ n →
      g.natDegree ≤ n - 2 ^ r ∨ 2 ^ r ≤ 2 * g.natDegree) → ¬ g ∣ polyP n

/-- Odd factors only at odd indices and outside the mod-four gap. -/
def H3 : Prop := ∀ n : ℕ, Odd n → 1 ≤ n → (¬ ∃ r : ℕ, n = 2 ^ r) →
  ∀ g : ℚ[X], g.Monic → 3 ≤ g.natDegree → g.natDegree ≤ (polyP n).natDegree / 2 →
    Odd g.natDegree → (∀ r : ℕ, 2 ^ r ≤ n →
      g.natDegree ≤ n - 2 ^ r ∨ 2 ^ r ≤ 2 * g.natDegree) → ¬ g ∣ polyP n

theorem main : H1 → H2 → H3 → OMA.R_OeisA115257_conjecture_R1.H1 := by
  intro quadratic evenFactors oddFactors n hn hn2 g hmonic hd hsize hdiv
  have hgap (r : ℕ) (hr : 2 ^ r ≤ n) :
      g.natDegree ≤ n - 2 ^ r ∨ 2 ^ r ≤ 2 * g.natDegree := by
    by_contra! h
    exact polyP_factor_degree_gap r n hr h.1 h.2 hdiv
  by_cases hd2 : g.natDegree = 2
  · have hn3 : 3 ≤ n := by
      by_contra! h
      apply hn2
      rcases show n = 1 ∨ n = 2 by omega with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    exact quadratic n hn3 g hmonic hd2 hdiv
  · rcases Nat.even_or_odd g.natDegree with he | ho
    · obtain ⟨d, hd'⟩ := he
      exact evenFactors n hn hn2 g hmonic (by omega) hsize ⟨d, hd'⟩ hgap hdiv
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | hno
      · rw [hm, ← two_mul] at hdiv
        exact (Nat.not_even_iff_odd.mpr ho) (even_index_factor_degree m hdiv)
      · exact oddFactors n hno hn hn2 g hmonic (by omega) hsize ho hgap hdiv

end OMA.R_OeisA115257_conjecture_R1_H1_R1
