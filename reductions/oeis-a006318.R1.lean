import OMAStatements.S_oeis_a006318
import Mathlib.FieldTheory.Finite.Extension

-- Credit: @Alewawa

/-!
Replace irreducibility of the reversed Schröder truncation by finite-field certificates.
Rabin's criterion gives one coprimality test per prime divisor of the degree.
At prime degree, splitting over the degree-n extension leaves only linear factors or
one full-degree factor, so it suffices to exclude base-field roots.
-/

open Finset Polynomial OMA.S_oeis_a006318

namespace OMA.R_oeis_a006318_R1

private theorem schroder_degree (p n : ℕ) [Fact p.Prime] :
    (schroderPoly p n).natDegree = n := by
  unfold schroderPoly
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · rw [finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [schroder]
    · intro k hk hne
      have hkn : k < n + 1 := mem_range.mp hk
      have h : n ≠ n - k := by omega
      simp [h]
    · simp

private theorem irreducible_of_full_degree_factor {K : Type*} [Field K]
    {f g : K[X]} (hf : f ≠ 0) (hg : Irreducible g)
    (hd : g ∣ f) (hdeg : g.natDegree = f.natDegree) : Irreducible f := by
  obtain ⟨u, rfl⟩ := hd
  have hu : u ≠ 0 := by rintro rfl; simp at hf
  rw [natDegree_mul hg.ne_zero hu] at hdeg
  have hzero : u.natDegree = 0 := by omega
  have hunit : IsUnit u := by
    rw [eq_C_of_natDegree_eq_zero hzero]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
      intro he
      exact hu ((eq_C_of_natDegree_eq_zero hzero).trans (by simp [he]))))
  exact (irreducible_mul_isUnit hunit).mpr hg

/-- Rabin's test, with one coprimality check for each prime divisor of the degree. -/
private theorem rabin {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hn : 0 < n) (hdeg : f.natDegree = n) :
    Irreducible f ↔
      f ∣ X ^ (p^n) - X ∧
      ∀ r : ℕ, r.Prime → r ∣ n → IsCoprime f (X ^ (p^(n/r)) - X) := by
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcriterion {g : (ZMod p)[X]} (hg : Irreducible g) (d : ℕ) :
      g.natDegree ∣ d ↔ g ∣ X ^ (p^d) - X := by
    simpa only [hcard] using hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := d)
  constructor
  · intro hf
    refine ⟨(hcriterion hf n).mp (hdeg ▸ dvd_rfl), ?_⟩
    intro r hr hrd
    rcases hf.isCoprime_or_dvd (X ^ (p^(n/r)) - X) with hc | hd
    · exact hc
    · have h := (hcriterion hf (n/r)).mpr hd
      rw [hdeg] at h
      have hpos : 0 < n/r := Nat.div_pos (Nat.le_of_dvd hn hrd) hr.pos
      exact (not_le_of_gt (Nat.div_lt_self hn hr.one_lt) (Nat.le_of_dvd hpos h)).elim
  · rintro ⟨hfull, hcop⟩
    have hfpos : 0 < f.natDegree := hdeg ▸ hn
    have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
    obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hfpos
    have hd : g.natDegree ∣ n := (hcriterion hg n).mpr (hgf.trans hfull)
    apply irreducible_of_full_degree_factor hf0 hg hgf
    rw [hdeg]
    obtain ⟨s, hs⟩ := hd
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; omega
    by_cases hs1 : s = 1
    · simpa [hs1] using hs.symm
    obtain ⟨r, hr, hrD⟩ := Nat.exists_prime_and_dvd hs1
    have hrN : r ∣ n := hs ▸ dvd_mul_of_dvd_right hrD _
    have hd' : g.natDegree ∣ n/r := by
      rw [hs, Nat.mul_div_assoc _ hrD]
      exact dvd_mul_right _ _
    exact (hg.not_isUnit ((hcop r hr hrN).isUnit_of_dvd' hgf
      ((hcriterion hg (n/r)).mp hd'))).elim

private theorem prime_degree_certificate {p n : ℕ} [Fact p.Prime]
    {f : (ZMod p)[X]} (hn : n.Prime) (hdeg : f.natDegree = n)
    (hfull : f ∣ X ^ (p^n) - X) (hroot : ∀ a : ZMod p, ¬ IsRoot f a) :
    Irreducible f := by
  have hfpos : 0 < f.natDegree := hdeg ▸ hn.pos
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
  obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hfpos
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hd : g.natDegree ∣ n := by
    apply hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    rw [hcard]
    exact hgf.trans hfull
  rcases (Nat.dvd_prime hn).mp hd with he | he
  · obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one (p := g) (by
      rw [degree_eq_natDegree hg.ne_zero, he, Nat.cast_one])
    exact (hroot a (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr ha).trans hgf))).elim
  · exact irreducible_of_full_degree_factor hf0 hg hgf (he.trans hdeg.symm)

/-- The degree-three case has an irreducible reduction at p = 3. -/
private theorem degree_three : Irreducible (schroderPoly 3 3) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [schroder_degree]
    simp
  · have h0 : schroder 0 = 1 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h1 : schroder 1 = 2 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h2 : schroder 2 = 6 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h3 : schroder 3 = 22 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    intro a
    have heval : (schroderPoly 3 3).eval a =
          a^3 + 2*a^2 + 6*a + 22 := by
      norm_num [schroderPoly, Finset.sum_range_succ, h0, h1, h2, h3]
    rw [IsRoot, heval]
    fin_cases a <;> decide

/-- At prime degrees, a modular certificate consists of complete splitting over
the extension of degree n and absence of roots in the base field. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n.Prime →
    ∃ p : ℕ, p.Prime ∧ p < n*(n+1) ∧
      schroderPoly p n ∣ (X ^ (p^n) - X : (ZMod p)[X]) ∧
      ∀ a : ZMod p, ¬ IsRoot (schroderPoly p n) a

/-- At composite degrees, choose a prime satisfying the full Rabin test. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → ¬ n.Prime →
    ∃ p : ℕ, p.Prime ∧ p < n*(n+1) ∧
      schroderPoly p n ∣ (X ^ (p^n) - X : (ZMod p)[X]) ∧
      ∀ r : ℕ, r.Prime → r ∣ n → IsCoprime (schroderPoly p n) (X ^ (p^(n/r)) - X)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006318.main := by
  intro h1 h2 n hn
  obtain rfl | hn' := eq_or_lt_of_le (show 3 ≤ n by omega)
  · exact ⟨3, by decide, by decide, degree_three⟩
  by_cases hp : n.Prime
  · obtain ⟨p, hpp, hsmall, hfull, hroot⟩ := h1 n hn' hp
    let : Fact p.Prime := ⟨hpp⟩
    exact ⟨p, hpp, hsmall, prime_degree_certificate hp (schroder_degree p n) hfull hroot⟩
  · obtain ⟨p, hpp, hsmall, hfull, hcop⟩ := h2 n hn' hp
    let : Fact p.Prime := ⟨hpp⟩
    exact ⟨p, hpp, hsmall, (rabin (by omega) (schroder_degree p n)).mpr ⟨hfull, hcop⟩⟩

/-- The two certificate conditions are also necessary in their respective degrees. -/
theorem certificate_equiv : (H1 ∧ H2) ↔ (type_of% @OMA.S_oeis_a006318.main) := by
  constructor
  · rintro ⟨h1,h2⟩
    exact main h1 h2
  · intro h
    constructor
    · intro n hn hprime
      obtain ⟨p, hp, hpbound, hirr⟩ := h n (by omega)
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨hfull, hcop⟩ := (rabin (by omega) (schroder_degree p n)).mp hirr
      refine ⟨p, hp, hpbound, hfull, fun a ha => ?_⟩
      have hc := hcop n hprime (dvd_refl n)
      rw [Nat.div_self hprime.pos, pow_one] at hc
      have hd : X - C a ∣ (X^p - X : (ZMod p)[X]) := by
        apply dvd_iff_isRoot.mpr
        simp [IsRoot, ZMod.pow_card]
      exact (irreducible_X_sub_C a).not_isUnit (hc.isUnit_of_dvd' (dvd_iff_isRoot.mpr ha) hd)
    · intro n hn _
      obtain ⟨p, hp, hpbound, hirr⟩ := h n (by omega)
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨hfull, hcop⟩ := (rabin (by omega) (schroder_degree p n)).mp hirr
      exact ⟨p, hp, hpbound, hfull, hcop⟩

end OMA.R_oeis_a006318_R1
