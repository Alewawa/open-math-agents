import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1

/-!
# Enumerating the index-one candidates by deficit

The deficit and the local Korselt quotient bound the smaller prime by a divisor
test. A perfect-square test recovers the larger prime. Quotient one also forces
both reconstructed primes to be one modulo three.
-/

-- Credit: @Alewawa

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H1_R1

private lemma deficit_divisor {A p q h y v : ℕ} (hA : 0 < A) (hp : 1 < p)
    (hpq : p < q) (hx : A * p = v * (q - 1) + h) (hy : A * q = y + h)
    (hquad : v * (q - 1) * (q + p) + 1 = A * p ^ 2)
    (hdiv : p - 1 ∣ y) : p - 1 ∣ (A + v) * (A - 1) := by
  let s := p - 1
  let t := q - 1
  have hs : s + 1 = p := Nat.sub_add_cancel hp.le
  have ht : t + 1 = q := Nat.sub_add_cancel (by omega)
  have hlinear : (A + v) * t = y + A * s := by
    have h₁ : A * (s + 1) = v * t + h := by rw [hs]; exact hx
    have h₂ : A * (t + 1) = y + h := by rw [ht]; exact hy
    nlinarith only [h₁, h₂]
  have hst : s ∣ (A + v) * t := by
    rw [hlinear]
    exact dvd_add hdiv (dvd_mul_left _ _)
  have hscaled : s ∣ (A + v) * (v * t * (q + p)) := by
    rw [show (A + v) * (v * t * (q + p)) = ((A + v) * t) * (v * (q + p)) by ring]
    exact dvd_mul_of_dvd_left hst _
  have hfactor : v * t * (q + p) = A * (p + 1) * s + (A - 1) := by
    have h₁ : A * (p + 1) * (s + 1) = A * (p + 1) * p := by rw [hs]
    have h₂ : A - 1 + 1 = A := Nat.sub_add_cancel hA
    change v * t * (q + p) + 1 = A * p ^ 2 at hquad
    nlinarith only [h₁, h₂, hquad]
  rw [hfactor, mul_add] at hscaled
  exact (Nat.dvd_add_right (dvd_mul_left s _ |>.mul_left (A + v))).mp hscaled

private lemma recover_from_discriminant {A p q v : ℕ} (hp : 1 ≤ p) (hpq : p < q)
    (hv : 0 < v) (hquad : v * (q - 1) * (q + p) + 1 = A * p ^ 2) :
    v ∣ A * p ^ 2 - 1 ∧
      (Nat.sqrt ((p + 1) ^ 2 + 4 * ((A * p ^ 2 - 1) / v)) - (p - 1)) / 2 = q := by
  have hnum : A * p ^ 2 - 1 = v * ((q - 1) * (q + p)) := by
    rw [← mul_assoc]
    omega
  have hquot : (A * p ^ 2 - 1) / v = (q - 1) * (q + p) := by
    rw [hnum, Nat.mul_div_cancel_left _ hv]
  refine ⟨⟨_, hnum⟩, ?_⟩
  have hdisc : (p + 1) ^ 2 + 4 * ((A * p ^ 2 - 1) / v) = (2 * q + (p - 1)) ^ 2 := by
    rw [hquot]
    nlinarith only [Nat.sub_add_cancel hp, Nat.sub_add_cancel (show 1 ≤ q by omega)]
  rw [hdisc, Nat.sqrt_eq']
  omega

private lemma mod_three_table :
    ∀ a b : ZMod 3, a * (a - 1) + 1 = b → b * a = 1 → a = 1 ∧ b = 1 := by
  decide

private lemma prime_mod_three_of_quadratic {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hqpos : 1 ≤ q) (hd : p ∣ q * (q - 1) + 1) : p % 3 = 1 := by
  have hpFact : Fact p.Prime := ⟨hp⟩
  have hz : (q : ZMod p) * ((q : ZMod p) - 1) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hqpos, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ p).mpr hd
  have hz3 : (-(q : ZMod p)) ^ 3 = 1 := by
    linear_combination -((q : ZMod p) + 1) * hz
  have hnon : -(q : ZMod p) ≠ 1 := by
    intro he
    have hneg : (q : ZMod p) = -1 := neg_eq_iff_eq_neg.mp he
    rw [hneg] at hz
    have hcast : ((3 : ℕ) : ZMod p) = 0 := by
      linear_combination hz
    exact (not_le_of_gt hp3) (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 3 p).mp hcast))
  have hnonzero : -(q : ZMod p) ≠ 0 := by
    intro he
    simp [he] at hz3
  have hthree : Fact (Nat.Prime 3) := ⟨by decide⟩
  have horder : orderOf (-(q : ZMod p)) = 3 := orderOf_eq_prime hz3 hnon
  have hdiv : 3 ∣ p - 1 := by
    rw [← horder, orderOf_dvd_iff_pow_eq_one]
    exact ZMod.pow_card_sub_one_eq_one hnonzero
  omega

private lemma quotient_one_residues {h p q y : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p < q) (h₁ : q * (q - 1) + 1 = h * p) (h₂ : p * y + 1 = h * q)
    (hy : p - 1 ∣ y) : p % 3 = 1 ∧ q % 3 = 1 ∧ h % 3 = 1 := by
  have hqpos : 1 ≤ q := by omega
  have hpmod := prime_mod_three_of_quadratic hp hp3 hqpos (h₁.symm ▸ dvd_mul_left p h)
  have hdiv : 3 ∣ p - 1 := by omega
  have hpcast : (p : ZMod 3) = 1 := by
    exact (ZMod.natCast_eq_natCast_iff' p 1 3).mpr hpmod
  have hycast : (y : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff y 3).mpr (hdiv.trans hy)
  have he₁ : (q : ZMod 3) * ((q : ZMod 3) - 1) + 1 = (h : ZMod 3) := by
    have he := congrArg (fun m : ℕ => (m : ZMod 3)) h₁
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hqpos, Nat.cast_one, hpcast, mul_one] using he
  have he₂ : (h : ZMod 3) * (q : ZMod 3) = 1 := by
    have he := congrArg (fun m : ℕ => (m : ZMod 3)) h₂
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hycast, mul_zero, zero_add] using he.symm
  obtain ⟨hqmod, hhmod⟩ := mod_three_table _ _ he₁ he₂
  exact ⟨hpmod, (ZMod.natCast_eq_natCast_iff' q 1 3).mp hqmod,
    (ZMod.natCast_eq_natCast_iff' h 1 3).mp hhmod⟩

private lemma quadratic_screen {h p q v r : ℕ} (hr : 1 < r) (hq : 1 ≤ q)
    (hrec : q * (v * (q - 1)) + 1 = h * p) (hrhp : r ∣ h * p) :
    ¬ r ∣ v ∧ IsSquare ((v : ZMod r) * ((v : ZMod r) - 4)) := by
  have hd : r ∣ q * (v * (q - 1)) + 1 := hrec.symm ▸ hrhp
  constructor
  · intro hv
    have ht : r ∣ q * (v * (q - 1)) := (dvd_mul_of_dvd_left hv _).mul_left _
    exact (not_le_of_gt hr) (Nat.le_of_dvd Nat.one_pos ((Nat.dvd_add_right ht).mp hd))
  · have hz : (q : ZMod r) * ((v : ZMod r) * ((q : ZMod r) - 1)) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one] using
        (ZMod.natCast_eq_zero_iff _ r).mpr hd
    refine ⟨2 * (v : ZMod r) * (q : ZMod r) - (v : ZMod r), ?_⟩
    linear_combination (-4 * (v : ZMod r)) * hz

private lemma quotient_ne_four {h p q v : ℕ} (hsq : Squarefree (h * p)) (hq : 1 < q)
    (hrec : q * (v * (q - 1)) + 1 = h * p) : v ≠ 4 := by
  intro hv
  have hCalc : ((q - 1) + 1) * (4 * (q - 1)) + 1 = h * p := by
    simpa only [Nat.sub_add_cancel hq.le, hv] using hrec
  have he : (2 * (q - 1) + 1) ^ 2 = h * p := by nlinarith only [hCalc]
  rw [← he] at hsq
  exact (by decide : (2 : ℕ) ≠ 1) ((Nat.squarefree_pow_iff (by omega) (by decide)).mp hsq).2

private lemma reduced_korselt {h p q v d : ℕ} (hq : 1 < q)
    (hrec : q * (v * (q - 1)) + 1 = h * p) (hd : d ∣ h * p * q - 1) :
    d / d.gcd (q - 1) ∣ v * q ^ 2 + 1 := by
  have hfact : (q - 1) * (v * q ^ 2 + 1) + 1 = h * p * q := by
    calc
      (q - 1) * (v * q ^ 2 + 1) + 1 = (q * (v * (q - 1)) + 1) * q := by
        nlinarith only [Nat.sub_add_cancel hq.le]
      _ = h * p * q := by rw [hrec]
  have hpred : h * p * q - 1 = (q - 1) * (v * q ^ 2 + 1) := by omega
  rw [hpred] at hd
  have hg := Nat.gcd_pos_of_pos_right d (show 0 < q - 1 by omega)
  exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left d _) hg).mpr
    (dvd_gcd_mul_iff_dvd_mul.mpr hd)

/-- The quotient-one search. Both reconstructed primes are one modulo three. -/
def H1 : Prop :=
  ∀ A p : ℕ, 2 < A → Odd A → A % 3 = 1 → p.Prime → p % 3 = 1 → p - 1 ∣ (A + 1) * (A - 1) →
    let q := (Nat.sqrt ((p + 1) ^ 2 + 4 * (A * p ^ 2 - 1)) - (p - 1)) / 2
    let h := A * p - (q - 1)
    let d := h.primeFactors.lcm (fun r => r - 1)
    p < q → q.Prime → q % 3 = 1 → q - 1 < h →
    1 < h → Odd h → Squarefree h → h < A ^ 3 →
    (q - 1) * (q + p) + 1 = A * p ^ 2 →
    A + (∑ r ∈ h.primeFactors, h / r) = h →
    (∀ r ∈ h.primeFactors, r < p) → (∀ r ∈ h.primeFactors, r % 3 = 1) →
    p - 1 ∣ A * q - h →
    ¬ (d / d.gcd (q - 1) ∣ q ^ 2 + 1)

/-- The larger quotients are bounded by the deficit and have a divisor and a
perfect-square test before the cofactor and its prime factors are examined. -/
def H2 : Prop :=
  ∀ A v p : ℕ, 2 ≤ v → v ≠ 4 → 2 * v < A → Odd A → p.Prime →
    p - 1 ∣ (A + v) * (A - 1) → v ∣ A * p ^ 2 - 1 →
    let q := (Nat.sqrt ((p + 1) ^ 2 + 4 * ((A * p ^ 2 - 1) / v)) - (p - 1)) / 2
    let h := A * p - v * (q - 1)
    let d := h.primeFactors.lcm (fun r => r - 1)
    p < q → q.Prime → v * (q - 1) < h →
    1 < h → Odd h → Squarefree h → h < A * ((A + v) * (A - 1) + 1) →
    v * (q - 1) * (q + p) + 1 = A * p ^ 2 →
    A + (∑ r ∈ h.primeFactors, h / r) = h →
    (∀ r ∈ h.primeFactors, r < p) →
    (∀ r ∈ insert p h.primeFactors, ¬ r ∣ v ∧ IsSquare ((v : ZMod r) * ((v : ZMod r) - 4))) →
    p - 1 ∣ A * q - h →
    ¬ (d / d.gcd (q - 1) ∣ v * q ^ 2 + 1)

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1.H1 := by
  intro hone hlarge h x y hh hodd hsq
  let L := ∑ r ∈ h.primeFactors, h / r
  let A := h - L % h
  let p := (x + h) / A
  let q := (y + h) / A
  change L < h → 0 < x → x < y → x < h → x * y + A = h ^ 2 → h < 2 * A ^ 3 →
    A ∣ x + h → A ∣ y + h → p.Prime → q.Prime → (∀ r ∈ h.primeFactors, r < p) →
    p - 1 ∣ y → q - 1 ∣ x → ¬ (h.primeFactors.lcm (fun r => r - 1) ∣ h * p * q - 1)
  intro hL hx0 hxy hxh hpair _hbound hdx hdy hp hq hprimes hdp hdq
  have hdef : A + L = h := by
    dsimp [A]
    rw [Nat.mod_eq_of_lt hL, Nat.sub_add_cancel hL.le]
  have hA : 0 < A := by omega
  have hx : A * p = x + h := by
    change A * ((x + h) / A) = x + h
    rw [mul_comm]
    exact Nat.div_mul_cancel hdx
  have hy : A * q = y + h := by
    change A * ((y + h) / A) = y + h
    rw [mul_comm]
    exact Nat.div_mul_cancel hdy
  have hpq : p < q := by
    by_contra! hqp
    have := Nat.mul_le_mul_left A hqp
    omega
  have hprod : A * p * q + 1 = h * p + h * q := by
    apply Nat.eq_of_mul_eq_mul_left hA
    calc
      A * (A * p * q + 1) = (A * p) * (A * q) + A := by ring
      _ = (x + h) * (y + h) + A := by rw [hx, hy]
      _ = h * (x + h) + h * (y + h) := by nlinarith only [hpair]
      _ = A * (h * p + h * q) := by rw [← hx, ← hy]; ring
  have hrecx : q * x + 1 = h * p := by
    have he : (x + h) * q = A * p * q := by rw [← hx]
    nlinarith only [he, hprod]
  have hrecy : p * y + 1 = h * q := by
    have he : p * (y + h) = A * p * q := by rw [← hy]; ring
    nlinarith only [he, hprod]
  obtain ⟨v, hvx⟩ := hdq
  rw [mul_comm] at hvx
  have hv : 0 < v := by
    by_contra! hv0
    simp [show v = 0 by omega] at hvx
    omega
  have hvbound : 2 * v < A := by
    apply Nat.lt_of_mul_lt_mul_right (a := p)
    have he : v * p ≤ x := by
      rw [hvx]
      exact Nat.mul_le_mul_left v (by omega)
    rw [hx]
    nlinarith only [he, hxh]
  have hquad : v * (q - 1) * (q + p) + 1 = A * p ^ 2 := by
    rw [← hvx]
    have he : A * p * p = (x + h) * p := by rw [hx]
    nlinarith only [he, hrecx]
  have hd := deficit_divisor hA hp.one_lt hpq (hvx ▸ hx) hy hquad hdp
  have hpbound : p ≤ (A + v) * (A - 1) + 1 := by
    have hle := Nat.le_of_dvd (Nat.mul_pos (show 0 < A + v by omega) (show 0 < A - 1 by omega)) hd
    omega
  have hhbound : h < A * ((A + v) * (A - 1) + 1) :=
    (show h < A * p by omega).trans_le (Nat.mul_le_mul_left A hpbound)
  have hAo : Odd A := by
    have hqo := Nat.odd_iff.mp (hq.odd_iff.mpr (by have := hp.two_le; omega))
    have hxmod : x % 2 = 0 := by
      rw [hvx, Nat.mul_mod, show (q - 1) % 2 = 0 by omega]
      simp
    apply Nat.odd_iff.mpr
    have he := congrArg (· % 2) hpair
    rw [pow_two, Nat.add_mod, Nat.mul_mod x y, hxmod, zero_mul, Nat.zero_mod, zero_add,
      Nat.mod_mod, Nat.mul_mod h h, Nat.odd_iff.mp hodd] at he
    exact he
  obtain ⟨hvdiv, hroot⟩ := recover_from_discriminant hp.one_le hpq hv hquad
  have hcofactor : A * p - v * (q - 1) = h := by rw [← hvx, hx]; omega
  have hy' : A * q - h = y := by rw [hy]; omega
  have hrec : q * (v * (q - 1)) + 1 = h * p := hvx ▸ hrecx
  have hcop : h.Coprime p := (hp.coprime_iff_not_dvd.mpr (fun hpd =>
    lt_irrefl p (hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)))).symm
  have hv4 := quotient_ne_four (Nat.squarefree_mul_iff.mpr ⟨hcop, hsq, hp.squarefree⟩)
    hq.one_lt hrec
  intro hKorselt
  have hlast := reduced_korselt hq.one_lt hrec hKorselt
  by_cases hv1 : v = 1
  · subst v
    have hp3 : 3 < p := by
      obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr hh
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hr2 : r ≠ 2 := by
        intro he
        have hd2 : 2 ∣ h := he ▸ Nat.dvd_of_mem_primeFactors hr
        exact hodd.not_two_dvd_nat hd2
      exact (show 3 ≤ r by have := hrp.two_le; omega).trans_lt (hprimes r hr)
    have hx' : x = q - 1 := by simpa only [one_mul] using hvx
    obtain ⟨hpmod, hqmod, hhmod⟩ := quotient_one_residues hp hp3 hpq (hx' ▸ hrecx) hrecy hdp
    have hAmod : A % 3 = 1 := by
      apply (ZMod.natCast_eq_natCast_iff' A 1 3).mp
      have hpcast := (ZMod.natCast_eq_natCast_iff' p 1 3).mpr hpmod
      have hqcast := (ZMod.natCast_eq_natCast_iff' q 1 3).mpr hqmod
      have hhcast := (ZMod.natCast_eq_natCast_iff' h 1 3).mpr hhmod
      have he := congrArg (fun m : ℕ => (m : ZMod 3)) (show A * p = (q - 1) + h from hx' ▸ hx)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hq.one_le, Nat.cast_one,
        hpcast, hqcast, hhcast, mul_one, sub_self, zero_add] using he
    have hsmallbound : h < A ^ 3 := by
      have hid : (A + 1) * (A - 1) + 1 = A ^ 2 := by
        nlinarith only [Nat.sub_add_cancel hA]
      simpa only [hid, pow_succ', pow_two, mul_assoc] using hhbound
    have hres : ∀ r ∈ h.primeFactors, r % 3 = 1 := by
      intro r hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrd := Nat.dvd_of_mem_primeFactors hr
      have hr2 : r ≠ 2 := fun e => hodd.not_two_dvd_nat (e ▸ hrd)
      have hr3 : r ≠ 3 := by
        intro e
        have hd3 : 3 ∣ h := e ▸ hrd
        omega
      apply prime_mod_three_of_quadratic hrp (by have := hrp.two_le; omega) hq.one_le
      rw [show q * (q - 1) + 1 = h * p by simpa only [one_mul] using hrec]
      exact dvd_mul_of_dvd_left hrd p
    have hcase := hone A p (by omega) hAo hAmod hp hpmod hd
    dsimp only at hcase
    have hroot' : (Nat.sqrt ((p + 1) ^ 2 + 4 * (A * p ^ 2 - 1)) - (p - 1)) / 2 = q := by
      simpa only [Nat.div_one] using hroot
    rw [hroot', show A * p - (q - 1) = h by simpa only [one_mul] using hcofactor, hy'] at hcase
    exact hcase hpq hq hqmod (by omega) hh hodd hsq hsmallbound (by simpa only [one_mul] using hquad) hdef
      hprimes hres hdp (by simpa only [one_mul] using hlast)
  · have hres : ∀ r ∈ insert p h.primeFactors, ¬ r ∣ v ∧
        IsSquare ((v : ZMod r) * ((v : ZMod r) - 4)) := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrOld
      · exact quadratic_screen hp.one_lt hq.one_le hrec (dvd_mul_left p h)
      · exact quadratic_screen (Nat.prime_of_mem_primeFactors hrOld).one_lt hq.one_le hrec
          (dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors hrOld) p)
    have hcase := hlarge A v p (by omega) hv4 hvbound hAo hp hd hvdiv
    dsimp only at hcase
    rw [hroot, hcofactor, hy'] at hcase
    exact hcase hpq hq (hvx ▸ hxh) hh hodd hsq hhbound hquad hdef hprimes hres hdp hlast

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H1_R1
