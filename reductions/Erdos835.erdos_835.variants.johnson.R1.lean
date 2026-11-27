import FormalConjectures.ErdosProblems.«835»

/-!
# Erdős Problem 835 via a distinguished point

A coloring of the sets through one point extends by complementation when
sets sharing only that point have distinct colors.
-/

-- Credit: @Alewawa

open Finset SimpleGraph

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R1

/-- Find an optimal coloring of the Johnson graph on the vertices through one point.
Deleting the distinguished point identifies this induced graph with J(2k-1,k-1). -/
def H1 : Prop :=
  ∃ (k : ℕ) (x : Fin (2 * k)), 3 ≤ k ∧ Even k ∧
    (J(2 * k, k).induce {v | x ∈ v.val}).Colorable (k + 1)

/-- Two blocks through the distinguished point that otherwise miss each other have
different colors in every optimal coloring of this induced graph.
This is Mendelsohn’s intersecting-block lemma, https://doi.org/10.4153/CJM-1970-117-0. -/
def H2 : Prop :=
  ∀ (k : ℕ) (x : Fin (2 * k)), 3 ≤ k → Even k →
    ∀ (c : (J(2 * k, k).induce {v | x ∈ v.val}).Coloring (Fin (k + 1)))
      (v w : {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val}),
      v.val.val ∩ w.val.val = {x} → c v ≠ c w

lemma clique_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ((k + 1 : ℕ) : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2 * k)))) (n := k - 1) (by simp; omega)
  let f (i : (sᶜ : Finset (Fin (2 * k)))) :
      {v : Finset (Fin (2 * k)) // v.card = k} :=
    ⟨insert i.val s, by
      rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp i.property), hs]
      omega⟩
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := ↑(sᶜ : Finset (Fin (2 * k))))
    (f := f)
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs]
    omega
  · intro i j hij
    have hi := Finset.mem_compl.mp i.property
    have hj := Finset.mem_compl.mp j.property
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have h : insert i.val s ∩ insert j.val s = s := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      by_cases hz : z ∈ s
      · simp [hz]
      · simp only [hz, or_false, iff_false, not_and]
        exact fun he hf => hne (he.symm.trans hf)
    change (insert i.val s ∩ insert j.val s).card + 1 = k
    rw [h, hs]
    omega

theorem main : H1 → H2 → type_of% @Erdos835.erdos_835.variants.johnson := by
  classical
  rintro ⟨k, x, hk, he, ⟨c⟩⟩ h₂
  have hcross := h₂ k x hk he c
  let C (v : {s : Finset (Fin (2 * k)) // s.card = k}) :
      {s : Finset (Fin (2 * k)) // s.card = k} :=
    ⟨v.valᶜ, by
      rw [Finset.card_compl, Fintype.card_fin, v.property]
      omega⟩
  let fold (v : {s : Finset (Fin (2 * k)) // s.card = k}) :
      {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val} :=
    if hv : x ∈ v.val then ⟨v, hv⟩ else ⟨C v, Finset.mem_compl.mpr hv⟩
  have hc : J(2 * k, k).Colorable (k + 1) := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => c (fold v)) ?_⟩
    intro v w h
    have hcard : (v.val ∩ w.val).card + 1 = k := h
    have hunion := Finset.card_union_add_card_inter v.val w.val
    rw [v.property, w.property] at hunion
    have hdiff : ∀ (a b : {s : Finset (Fin (2 * k)) // s.card = k}),
        x ∈ a.val → x ∉ b.val → (a.val ∩ b.val).card + 1 = k →
        a.val ∩ b.valᶜ = {x} := by
      intro a b ha hb hab
      have hcount := Finset.card_sdiff_of_subset (Finset.inter_subset_left : a.val ∩ b.val ⊆ a.val)
      rw [a.property] at hcount
      have hset : a.val \ (a.val ∩ b.val) = a.val ∩ b.valᶜ := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
        tauto
      rw [hset] at hcount
      have hsingle : (a.val ∩ b.valᶜ).card = 1 := by omega
      symm
      exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr
        (Finset.mem_inter.mpr ⟨ha, Finset.mem_compl.mpr hb⟩)) (by simp [hsingle])
    by_cases hv : x ∈ v.val <;> by_cases hw : x ∈ w.val
    · simpa only [fold, dif_pos hv, dif_pos hw] using
        (c.valid (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) h)
    · simpa only [fold, dif_pos hv, dif_neg hw] using
        (hcross ⟨v, hv⟩ ⟨C w, Finset.mem_compl.mpr hw⟩ (hdiff v w hv hw hcard))
    · have hwv : (w.val ∩ v.val).card + 1 = k := by simpa only [inter_comm] using hcard
      simpa only [fold, dif_neg hv, dif_pos hw] using
        (hcross ⟨w, hw⟩ ⟨C v, Finset.mem_compl.mpr hv⟩ (hdiff w v hw hv hwv)).symm
    · have hcompl : J(2 * k, k).Adj (C v) (C w) := by
        change (v.valᶜ ∩ w.valᶜ).card + 1 = k
        rw [← Finset.compl_union, Finset.card_compl, Fintype.card_fin]
        omega
      simpa only [fold, dif_neg hv, dif_neg hw] using
        (c.valid (v := ⟨C v, Finset.mem_compl.mpr hv⟩)
          (w := ⟨C w, Finset.mem_compl.mpr hw⟩) hcompl)
  refine ⟨k - 3, ?_⟩
  have hshift : k - 3 + 3 = k := by omega
  change J(2 * (k - 3 + 3), k - 3 + 3).chromaticNumber =
    ((k - 3 + 3 : ℕ) : ℕ∞) + 1
  rw [hshift, ← Nat.cast_add_one]
  exact le_antisymm hc.chromaticNumber_le (clique_lower_bound k hk)

end OMA.R_Erdos835_erdos_835_variants_johnson_R1
