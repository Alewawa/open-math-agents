import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1

-- Credit: @Alewawa

open Finset SimpleGraph

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

/-- Color only blocks containing x and avoiding y. Deleting x gives J(2k-2,k-1).
The coloring is specified on all finsets for convenience, but the condition only
uses its values on this slice. -/
def H1 : Prop :=
  ∃ (k : ℕ) (x y : Fin (2 * k)), 3 ≤ k ∧ Even k ∧ x ≠ y ∧
    ∃ c : Finset (Fin (2 * k)) → Fin (k + 1),
      ∀ s : Finset (Fin (2 * k)), s.card + 1 = k → x ∈ s → y ∉ s →
        ∀ a ∉ s, ∀ b ∉ s, a ≠ y → b ≠ y → a ≠ b → c (insert a s) ≠ c (insert b s)

/-- In a proper edge coloring of the complete graph on k+1 vertices with k+1
colors, for k even, different vertices miss different colors. The diagonal is unused. -/
def H2 : Prop :=
  ∀ (k : ℕ), Even k → ∀ (Q : Finset (Fin (2 * k))), Q.card = k + 1 →
    ∀ e : Fin (2 * k) → Fin (2 * k) → Fin (k + 1),
      (∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a) →
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ d ∈ Q, b ≠ a → d ≠ a → b ≠ d → e a b ≠ e a d) →
      ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → ∀ i j : Fin (k + 1),
        (∀ t ∈ Q, t ≠ a → i ≠ e a t) → (∀ t ∈ Q, t ≠ b → j ≠ e b t) → i ≠ j

lemma missing_color {k : ℕ} (c : Finset (Fin (2 * k)) → Fin (k + 1))
    (s : Finset (Fin (2 * k))) (y : Fin (2 * k)) (hs : s.card + 1 = k) (hy : y ∉ s) :
    ∃ i : Fin (k + 1), ∀ a ∉ s, a ≠ y → i ≠ c (insert a s) := by
  classical
  let q := (insert y s)ᶜ
  have hq : q.card = k := by
    change ((insert y s)ᶜ).card = k
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hy]
    omega
  let used := q.image (fun a => c (insert a s))
  have hle : used.card ≤ k := (Finset.card_image_le).trans_eq hq
  have hne : used ≠ univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨i, hi⟩ := Classical.not_forall.mp (Finset.eq_univ_iff_forall.not.mp hne)
  refine ⟨i, fun a ha hay h => hi ?_⟩
  exact Finset.mem_image.mpr ⟨a, by simpa [q, hay] using ha, h.symm⟩

lemma insert_repr {α : Type*} [DecidableEq α] {s v : Finset α}
    (h : s ⊆ v) (hc : s.card + 1 = v.card) : ∃ a ∉ s, v = insert a s := by
  have hd : (v \ s).card = 1 := by rw [Finset.card_sdiff_of_subset h]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hd
  have ham : a ∈ v \ s := by simp [ha]
  obtain ⟨hav, has⟩ := Finset.mem_sdiff.mp ham
  refine ⟨a, has, (Finset.eq_of_subset_of_card_le (Finset.insert_subset hav h) ?_).symm⟩
  rw [Finset.card_insert_of_notMem has, hc]

theorem main : H1 → H2 → OMA.R_Erdos835_erdos_835_variants_johnson_R1.H1 := by
  classical
  rintro ⟨k, x, y, hk, he, hxy, c, hc⟩ hp
  let m (s : Finset (Fin (2 * k))) : Fin (k + 1) :=
    if h : s.card + 1 = k ∧ y ∉ s then (missing_color c s y h.1 h.2).choose else 0
  have hm (s : Finset (Fin (2 * k))) (hs : s.card + 1 = k) (hy : y ∉ s) :
      ∀ a ∉ s, a ≠ y → m s ≠ c (insert a s) := by
    simpa only [m, dif_pos (And.intro hs hy)] using (missing_color c s y hs hy).choose_spec
  let f (v : Finset (Fin (2 * k))) := if y ∈ v then m (v.erase y) else c v
  refine ⟨k, x, hk, he, ⟨SimpleGraph.Coloring.mk (fun v => f v.val.val) ?_⟩⟩
  intro v w hvw
  let s := v.val.val ∩ w.val.val
  have hs : s.card + 1 = k := hvw
  have hx : x ∈ s := Finset.mem_inter.mpr ⟨v.property, w.property⟩
  obtain ⟨a, ha, hv⟩ := insert_repr (s := s) (v := v.val.val)
    Finset.inter_subset_left (hs.trans v.val.property.symm)
  obtain ⟨b, hb, hw⟩ := insert_repr (s := s) (v := w.val.val)
    Finset.inter_subset_right (hs.trans w.val.property.symm)
  have hab : a ≠ b := by
    intro h
    apply ha
    exact Finset.mem_inter.mpr ⟨by rw [hv]; exact Finset.mem_insert_self _ _,
      by rw [hw, h]; exact Finset.mem_insert_self _ _⟩
  change f v.val.val ≠ f w.val.val
  rw [hv, hw]
  by_cases hy : y ∈ s
  · let r := s.erase y
    have hry : y ∉ r := Finset.notMem_erase _ _
    have hrx : x ∈ r := Finset.mem_erase.mpr ⟨hxy, hx⟩
    have hr : r.card + 1 = s.card := by
      have hpos := Finset.card_pos.mpr ⟨y, hy⟩
      simp only [r, Finset.card_erase_of_mem hy]
      omega
    have hrsub : r ⊆ s := Finset.erase_subset _ _
    have outside_y {u : Fin (2 * k)} (hu : u ∉ s) : u ≠ y := fun h => hu (h ▸ hy)
    have outside_insert {t u : Fin (2 * k)} (ht : t ∉ s) (htu : t ≠ u) :
        t ∉ insert u r := fun h => (Finset.mem_insert.mp h).elim htu (fun h => ht (hrsub h))
    have yfree {u : Fin (2 * k)} (hu : u ∉ s) : y ∉ insert u r :=
      fun h => (Finset.mem_insert.mp h).elim (outside_y hu).symm hry
    let e (u t : Fin (2 * k)) := c (insert t (insert u r))
    have row (u : Fin (2 * k)) (hu : u ∉ s) :
        ∀ t ∉ s, ∀ d ∉ s, t ≠ u → d ≠ u → t ≠ d → e u t ≠ e u d := by
      intro t ht d hd htu hdu htd
      have hur : u ∉ r := fun h => hu (hrsub h)
      exact hc (insert u r) (by simpa only [Finset.card_insert_of_notMem hur, hr] using hs)
        (Finset.mem_insert_of_mem hrx) (yfree hu) t (outside_insert ht htu) d
        (outside_insert hd hdu) (outside_y ht) (outside_y hd) htd
    have gap (u : Fin (2 * k)) (hu : u ∉ s) :
        ∀ t ∈ sᶜ, t ≠ u → m (insert u r) ≠ e u t := by
      intro t ht htu
      have hur : u ∉ r := fun h => hu (hrsub h)
      have ht' := Finset.mem_compl.mp ht
      exact hm (insert u r) (by simpa only [Finset.card_insert_of_notMem hur, hr] using hs)
        (yfree hu) t (outside_insert ht' htu) (outside_y ht')
    have hQ : (sᶜ).card = k + 1 := by rw [Finset.card_compl, Fintype.card_fin]; omega
    have hdiff := hp k he sᶜ hQ e (fun u _ t _ => by simp [e, Finset.insert_comm])
      (fun u hu t ht d hd => row u (Finset.mem_compl.mp hu) t (Finset.mem_compl.mp ht) d
        (Finset.mem_compl.mp hd))
      a (Finset.mem_compl.mpr ha) b (Finset.mem_compl.mpr hb) hab _ _ (gap a ha) (gap b hb)
    have hay : a ≠ y := fun h => ha (h ▸ hy)
    have hby : b ≠ y := fun h => hb (h ▸ hy)
    simpa [f, hy, Finset.erase_insert_of_ne hay, Finset.erase_insert_of_ne hby, r] using hdiff
  · by_cases hay : a = y
    · subst a
      simpa [f, hy, Ne.symm hab, hab] using hm s hs hy b hb hab.symm
    · by_cases hby : b = y
      · subst b
        simpa [f, hy, Ne.symm hab, hab] using (hm s hs hy a ha hab).symm
      · simpa [f, hy, Ne.symm hay, Ne.symm hby] using hc s hs hx hy a ha b hb hay hby hab

/-- Each color is a matching on an odd number of vertices, so misses at least
one vertex. Every vertex misses precisely one color, forcing a bijection. -/
lemma odd_clique_missing_colors : H2 := by
  classical
  intro k he Q hQ e hsym hproper
  let used (a : Q) := (Q.erase a.val).image (e a.val)
  have hsingle (a : Q) : ((used a)ᶜ).card = 1 := by
    have hc : (used a).card = (Q.erase a.val).card := by
      apply Finset.card_image_of_injOn
      intro b hb d hd h
      obtain ⟨hba, hbQ⟩ := Finset.mem_erase.mp hb
      obtain ⟨hda, hdQ⟩ := Finset.mem_erase.mp hd
      exact Classical.byContradiction fun hbd =>
        hproper a a.property b hbQ d hdQ hba hda hbd h
    rw [Finset.card_compl, Fintype.card_fin, hc, Finset.card_erase_of_mem a.property, hQ]
    omega
  have unique (a : Q) := Finset.card_eq_one_iff_existsUnique.mp (hsingle a)
  let m (a : Q) := (unique a).exists.choose
  have hm (a : Q) : m a ∈ (used a)ᶜ := (unique a).exists.choose_spec
  have missing_eq (a : Q) (i : Fin (k + 1))
      (hi : ∀ t ∈ Q, t ≠ a.val → i ≠ e a.val t) : m a = i := by
    apply (unique a).unique (hm a)
    apply Finset.mem_compl.mpr
    intro h
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp h
    exact hi t (Finset.mem_erase.mp ht).2 (Finset.mem_erase.mp ht).1 hti.symm
  have onto : Function.Surjective m := by
    intro i
    by_contra! hn
    let G : SimpleGraph Q :=
      { Adj := fun a b => a.val ≠ b.val ∧ e a.val b.val = i
        symm := ⟨fun a b h => ⟨h.1.symm, (hsym b b.property a a.property).trans h.2⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    have degree_one (a : Q) : G.degree a = 1 := by
      apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      have hex : ∃ t ∈ Q, t ≠ a.val ∧ i = e a.val t := by
        by_contra! hh
        exact hn a (missing_eq a i hh)
      obtain ⟨t, ht, hta, hi⟩ := hex
      refine ⟨⟨t, ht⟩, ⟨hta.symm, hi.symm⟩, ?_⟩
      intro d hd
      apply Subtype.ext
      by_contra hdt
      exact hproper a a.property d d.property t ht hd.1.symm hta hdt (hd.2.trans hi)
    have hs := G.sum_degrees_eq_twice_card_edges
    simp only [degree_one, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hQ,
      smul_eq_mul, mul_one] at hs
    obtain ⟨l, hl⟩ := he
    omega
  have hinj := ((Fintype.bijective_iff_surjective_and_card m).mpr
    ⟨onto, by simp [hQ]⟩).1
  intro a ha b hb hab i j hi hj hij
  have h := (missing_eq ⟨a, ha⟩ i hi).trans (hij.trans (missing_eq ⟨b, hb⟩ j hj).symm)
  exact hab (congrArg Subtype.val (hinj h))

/-- Restriction to the blocks avoiding a second point gives the converse. -/
lemma restrict_coloring : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H1 → H1 := by
  classical
  rintro ⟨k, x, hk, he, ⟨C⟩⟩
  have : Nontrivial (Fin (2 * k)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨y, hy⟩ := exists_ne x
  let c (v : Finset (Fin (2 * k))) : Fin (k + 1) :=
    if h : v.card = k ∧ x ∈ v then C ⟨⟨v, h.1⟩, h.2⟩ else 0
  refine ⟨k, x, y, hk, he, hy.symm, c, ?_⟩
  intro s hs hx _ a ha b hb _ _ hab
  have block (t : Fin (2 * k)) (ht : t ∉ s) :
      (insert t s).card = k ∧ x ∈ insert t s :=
    ⟨(Finset.card_insert_of_notMem ht).trans hs, Finset.mem_insert_of_mem hx⟩
  have inter : insert a s ∩ insert b s = s := by
    ext t
    simp only [Finset.mem_inter, Finset.mem_insert]
    grind
  simp only [c, dif_pos (block a ha), dif_pos (block b hb)]
  apply C.valid
  change (insert a s ∩ insert b s).card + 1 = k
  rwa [inter]

theorem slice_iff : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H1 ↔ H1 :=
  ⟨restrict_coloring, fun h => main h odd_clique_missing_colors⟩

end OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1
