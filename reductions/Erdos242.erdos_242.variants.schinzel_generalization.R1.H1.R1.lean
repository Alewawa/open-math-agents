import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1

open Filter
open scoped BigOperators

namespace OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1

private theorem scale {a d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (h : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / d : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  have hmpos : 0 < m := by
    by_contra! hzero
    have : m = 0 := by omega
    simp [this] at hm
    omega
  refine ⟨x * m, y * m, z * m, Nat.mul_pos hx hmpos,
    Nat.mul_lt_mul_of_pos_right hxy hmpos, Nat.mul_lt_mul_of_pos_right hyz hmpos, ?_⟩
  simpa only [hm, Nat.cast_mul, div_div, add_div] using
    congrArg (fun q : ℚ => q / (m : ℚ)) heq

-- Large primes in the residual classes.
def H1 : Prop :=
  ∀ a : ℕ, 4 ≤ a →
    ∀ᶠ p : ℕ in atTop, p.Prime → 0 < p % a ∧ p % a + 2 < a →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (a / p : ℚ) = 1 / x + 1 / y + 1 / z

-- An exceptional prime whose powers stay in the residual classes needs one solved power.
def H2 : Prop :=
  ∀ a p : ℕ, 4 ≤ a → p.Prime →
    (∀ k : ℕ, 2 * a ≤ p ^ k → 0 < p ^ k % a ∧ p ^ k % a + 2 < a) →
    (¬ ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / p : ℚ) = 1 / x + 1 / y + 1 / z) →
    ∃ k x y z : ℕ, 2 ≤ k ∧ 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / (p ^ k : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H1 := by
  classical
  intro hPrime hPower a ha
  let Admissible (n : ℕ) : Prop :=
    ∀ d : ℕ, d ∣ n → 2 * a ≤ d → 0 < d % a ∧ d % a + 2 < a
  let Splits (n : ℕ) : Prop :=
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / n : ℚ) = 1 / x + 1 / y + 1 / z
  change ∀ᶠ n : ℕ in atTop, Admissible n → Splits n
  obtain ⟨B, hB⟩ := eventually_atTop.1 (hPrime a ha)
  have hExponent : ∀ p : ℕ, ∃ k : ℕ, p.Prime →
      ∀ n : ℕ, 0 < n → Admissible n → p ^ k ∣ n → Splits n := by
    intro p
    by_cases hp : p.Prime
    · by_cases hSplit : Splits p
      · exact ⟨1, fun _ _ hn _ hd => scale hn (by simpa only [pow_one] using hd) hSplit⟩
      · by_cases hAllowed : ∀ k : ℕ, 2 * a ≤ p ^ k → 0 < p ^ k % a ∧ p ^ k % a + 2 < a
        · obtain ⟨k, x, y, z, _, hx, hxy, hyz, heq⟩ := hPower a p ha hp hAllowed hSplit
          exact ⟨k, fun _ _ hn _ hd => scale hn hd ⟨x, y, z, hx, hxy, hyz, heq⟩⟩
        · obtain ⟨k, hk⟩ := not_forall.mp hAllowed
          exact ⟨k, fun _ _ _ hn hd => (hk fun hs => hn (p ^ k) hd hs).elim⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose exponent hExponent using hExponent
  let smallPrimes := (Finset.range (max B (2 * a))).filter Nat.Prime
  let C := ∏ p ∈ smallPrimes, p ^ exponent p
  refine eventually_atTop.2 ⟨C + 1, ?_⟩
  intro n hn hAllowed
  by_contra hNoSplit
  have hnpos : 0 < n := by omega
  have hSupport : n.primeFactors ⊆ smallPrimes := by
    intro p hp
    obtain ⟨hPrimeP, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hPrimeP⟩
    by_contra! hLarge
    have hBp : B ≤ p := le_trans (le_max_left _ _) hLarge
    have hap : 2 * a ≤ p := le_trans (le_max_right _ _) hLarge
    exact hNoSplit (scale hnpos hpdvd (hB p hBp hPrimeP (hAllowed p hpdvd hap)))
  have hBound : n ≤ C := calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hnpos)
    _ ≤ ∏ p ∈ n.primeFactors, p ^ exponent p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hPrimeP := (Nat.mem_primeFactors.mp hp).1
      apply Nat.pow_le_pow_right hPrimeP.pos
      by_contra! hTooLarge
      exact hNoSplit (hExponent p hPrimeP n hnpos hAllowed
        ((hPrimeP.pow_dvd_iff_le_factorization (Nat.ne_of_gt hnpos)).2 (le_of_lt hTooLarge)))
    _ ≤ C := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hSupport
      intro p hp _
      have hPrimeP := (Finset.mem_filter.mp hp).2
      exact Nat.one_le_pow _ _ hPrimeP.pos
  omega

end OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1
