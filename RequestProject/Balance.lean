module

public import RequestProject.Boundary
public import RequestProject.Cochain

@[expose] public section

/-!
# The binomial degree balance (Lemma 5 and identity (18), algebraic form)

For a generic `q` and a matching `m`, let `o_M = simplexIndex (vvec q m)` be the oriented
index of the inner simplex `H⁰(Δ^5)` along `m`, and for a facet `J_i` (all colors but `i`) and
an anchor row set `P`, let `φ_P(J_i)` be the index of the simplex `[u_P, v_j : j ∈ J_i]`.

* `lemma5`: `o_M = ∑ i, (-1)^i φ_P(J_i)` for every nonempty proper `P`;
* `degree_balance`: `o_M = ∑ i, (-1)^i (Φ₁ + Φ₂ - Φ₃)(J_i)`, where `Φ_k` sums `φ_P` over all
  `k`-subsets `P`; this is `(1 - 6 - 15 + 20) o_M = 0` rearranged;
* `facetIndex_congr`: `φ_P(J_i)` only depends on the letters of the matching in the colors of
  `J_i` (it is a facet-local quantity);
* `sum_rowSet_eq`: summing over anchor label sets `A` is the same as summing over row sets `P`.
-/

open Matrix

namespace Tverberg6R

/-- Enumerating the complement of two distinct colors. -/
lemma exists_enum_compl_pair {k₁ k₂ : Fin 6} (hk : k₁ ≠ k₂) :
    ∃ c : Fin 4 → Fin 6, Function.Injective c ∧ (∀ t, c t ≠ k₁ ∧ c t ≠ k₂) ∧
      ∀ s, s ≠ k₁ → s ≠ k₂ → ∃ t, c t = s := by
  classical
  set S : Finset (Fin 6) := Finset.univ \ {k₁, k₂} with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_univ_diff, Finset.card_pair hk]; simp
  refine ⟨S.orderEmbOfFin hScard, (S.orderEmbOfFin hScard).injective, fun t => ?_,
    fun s h1 h2 => ?_⟩
  · have := Finset.orderEmbOfFin_mem S hScard t
    simp only [hS, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at this
    exact this
  · have hs : s ∈ S := by simp [hS, h1, h2]
    have : s ∈ Set.range (S.orderEmbOfFin hScard) := by
      rw [Finset.range_orderEmbOfFin]; exact hs
    exact this

lemma sum_enum {c : Fin 4 → Fin 6} (hc : Function.Injective c) {k₁ k₂ : Fin 6}
    (hsurj : ∀ s, s ≠ k₁ → s ≠ k₂ → ∃ t, c t = s) {β : Type} [AddCommMonoid β]
    (f : Fin 6 → β) (h₁ : f k₁ = 0) (h₂ : f k₂ = 0) : ∑ i, f i = ∑ t, f (c t) := by
  classical
  rw [← Finset.sum_image (f := f) (fun a _ b _ h => hc h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  by_cases e1 : s = k₁
  · rw [e1, h₁]
  by_cases e2 : s = k₂
  · rw [e2, h₂]
  obtain ⟨t, rfl⟩ := hsurj s e1 e2
  exact (hs (Finset.mem_image_of_mem _ (Finset.mem_univ t))).elim

/-- The seven points `u_P, v_0, …, v_5`. -/
def sevenPts (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6)) :
    Fin 7 → Fin 5 → ℝ :=
  Fin.cons (uvec P) (vvec q m)

/-- Oriented index of the inner simplex along `m`. -/
noncomputable def innerIndex (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) : ℤ :=
  simplexIndex (vvec q m)

/-- Oriented index `φ_P(J_i)` of the anchor simplex over the facet `J_i`. -/
noncomputable def facetIndex (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6))
    (i : Fin 6) : ℤ :=
  simplexIndex (Fin.cons (uvec P) (fun t => vvec q m (i.succAbove t)) : Fin 6 → Fin 5 → ℝ)

lemma nIndep_sevenPts {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {P : Finset (Fin 6)} (hP1 : P.Nonempty) (hP2 : P ≠ Finset.univ) :
    NIndep (sevenPts q m P) := by
  -- the case where the coefficient of `u_P` vanishes
  have caseU : ∀ x : Fin 7 → ℝ, ∑ k, x k • sevenPts q m P k = 0 → x 0 = 0 →
      ∀ b : Fin 6, x b.succ = 0 → x = 0 := by
    intro x hx h0 b hb
    rw [Fin.sum_univ_succ, h0, zero_smul, zero_add] at hx
    simp only [sevenPts, Fin.cons_succ] at hx
    rw [Fin.sum_univ_succAbove _ b, hb, zero_smul, zero_add] at hx
    have hz := coeff_eq_zero_of_det_ne_zero (fun s => vvec q m (b.succAbove s))
      (hq.five m hm _ Fin.succAbove_right_injective) (fun s => x (b.succAbove s).succ) hx
    funext k
    refine Fin.cases h0 (fun s => ?_) k
    rcases Fin.eq_self_or_eq_succAbove b s with rfl | ⟨t, rfl⟩
    · exact hb
    · exact congrFun hz t
  intro x hx a b hab ha hb
  refine Fin.cases ?_ (fun a' => ?_) a ha hab
  · intro ha0 hab0
    obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.2 (Ne.symm hab0)
    exact caseU x hx ha0 b' hb
  · intro ha' hab'
    refine Fin.cases ?_ (fun b' => ?_) b hb hab'
    · intro hb0 _
      exact caseU x hx hb0 a' ha'
    · intro hb' hab''
      have hne : a' ≠ b' := fun h => hab'' (by rw [h])
      obtain ⟨c, hc, hcavoid, hcsurj⟩ := exists_enum_compl_pair hne
      rw [Fin.sum_univ_succ] at hx
      simp only [sevenPts, Fin.cons_zero, Fin.cons_succ] at hx
      rw [sum_enum hc hcsurj (fun s => x s.succ • vvec q m s) (by simp [ha'])
        (by simp [hb'])] at hx
      have hz := coeff_eq_zero_of_det_ne_zero
        (Fin.cons (uvec P) (fun t => vvec q m (c t)) : Fin 5 → Fin 5 → ℝ)
        (hq.anchor m hm P hP1 hP2 c hc) (Fin.cons (x 0) (fun t => x (c t).succ))
        (by rw [Fin.sum_univ_succ]; simpa using hx)
      funext k
      refine Fin.cases (by simpa using congrFun hz 0) (fun s => ?_) k
      by_cases e1 : s = a'
      · rw [e1]; exact ha'
      by_cases e2 : s = b'
      · rw [e2]; exact hb'
      obtain ⟨t, rfl⟩ := hcsurj s e1 e2
      simpa using congrFun hz t.succ

/-- **Lemma 5.** For every nonempty proper row set `P`,
`o_M = ∑ i, (-1)^i φ_P(J_i)`. -/
theorem lemma5 {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {P : Finset (Fin 6)} (hP1 : P.Nonempty) (hP2 : P ≠ Finset.univ) :
    innerIndex q m = ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetIndex q m P i := by
  have hdet : (affMat (sevenPts q m P ∘ (0 : Fin 7).succAbove)).det ≠ 0 := by
    have : sevenPts q m P ∘ (0 : Fin 7).succAbove = vvec q m := by
      funext s; simp [sevenPts]
    rw [this]
    exact hq.affine m hm
  have h := alternating_simplexIndex (nIndep_sevenPts hq hm hP1 hP2) hdet
  rw [Fin.sum_univ_succ] at h
  have e0 : sevenPts q m P ∘ (0 : Fin 7).succAbove = vvec q m := by
    funext s; simp [sevenPts]
  have es : ∀ i : Fin 6, sevenPts q m P ∘ i.succ.succAbove =
      (Fin.cons (uvec P) (fun t => vvec q m (i.succAbove t)) : Fin 6 → Fin 5 → ℝ) := by
    intro i
    funext s
    refine Fin.cases ?_ (fun t => ?_) s
    · simp [sevenPts]
    · simp [sevenPts, Fin.succ_succAbove_succ]
  simp only [e0, es, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at h
  unfold innerIndex facetIndex
  have : ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * (-1) *
      simplexIndex (Fin.cons (uvec P) (fun t => vvec q m (i.succAbove t)) :
        Fin 6 → Fin 5 → ℝ) =
      -∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) *
      simplexIndex (Fin.cons (uvec P) (fun t => vvec q m (i.succAbove t)) :
        Fin 6 → Fin 5 → ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this] at h
  linarith

/-- The sum of `φ_P(J_i)` over all row sets of size `k`. -/
noncomputable def facetSum (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (k : ℕ) (i : Fin 6) :
    ℤ :=
  ∑ P ∈ Finset.univ.powersetCard k, facetIndex q m P i

lemma sum_alternating_facetSum {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetSum q m k i = (Nat.choose 6 k : ℤ) * innerIndex q m := by
  unfold facetSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ P ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 6)),
      ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetIndex q m P i = innerIndex q m := by
    intro P hP
    rw [Finset.mem_powersetCard] at hP
    have hP1 : P.Nonempty := by rw [← Finset.card_pos]; omega
    have hP2 : P ≠ Finset.univ := by
      intro h; rw [h] at hP; simp at hP; omega
    exact (lemma5 hq hm hP1 hP2).symm
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard]
  simp

/-- **Identity (18).** With `Φ_k(J) = ∑_{|P| = k} φ_P(J)`,
`o_M = ∑ i, (-1)^i (Φ₁ + Φ₂ - Φ₃)(J_i)`; equivalently the corrected degree
`(1 - 6 - 15 + 20) o_M` vanishes. -/
theorem degree_balance {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) :
    innerIndex q m - ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) *
      (facetSum q m 1 i + facetSum q m 2 i - facetSum q m 3 i) = 0 := by
  have h1 := sum_alternating_facetSum hq hm (k := 1) le_rfl (by norm_num)
  have h2 := sum_alternating_facetSum hq hm (k := 2) (by norm_num) (by norm_num)
  have h3 := sum_alternating_facetSum hq hm (k := 3) (by norm_num) (by norm_num)
  have : ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) *
      (facetSum q m 1 i + facetSum q m 2 i - facetSum q m 3 i) =
      ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetSum q m 1 i +
      ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetSum q m 2 i -
      ∑ i : Fin 6, (-1 : ℤ) ^ (i : ℕ) * facetSum q m 3 i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, h1, h2, h3]
  norm_num [Nat.choose]
  ring

/-- `φ_P(J_i)` is facet-local: it only depends on the letters of the matching in the colors
other than `i`. -/
lemma facetIndex_congr (q : Fin 6 → Fin 6 → ℝ) {m m' : Fin 6 → Word} (P : Finset (Fin 6))
    (i : Fin 6) (h : ∀ r j, j ≠ i → m r j = m' r j) :
    facetIndex q m P i = facetIndex q m' P i := by
  unfold facetIndex
  congr 2
  funext t r
  simp [vvec, ell, colorTable, h _ _ (Fin.succAbove_ne i t)]

/-- Summing over anchor label sets `A` of size `k` equals summing over row sets `P`. -/
lemma sum_rowSet_eq {m : Fin 6 → Word} (hm : IsMatching m) (j₀ : Fin 6) (k : ℕ)
    (g : Finset (Fin 6) → ℤ) :
    ∑ A ∈ Finset.univ.powersetCard k, g (rowSet m j₀ A) =
      ∑ P ∈ Finset.univ.powersetCard k, g P := by
  have hbij : Function.Bijective (fun r => m r j₀) :=
    (Finite.injective_iff_bijective).mp (hm j₀)
  apply Finset.sum_nbij' (fun A => rowSet m j₀ A) (fun P => P.image (fun r => m r j₀))
  · intro A hA
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hA ⊢
    rw [card_rowSet hm, hA]
  · intro P hP
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hP ⊢
    rw [Finset.card_image_of_injective _ hbij.1]; exact hP
  · intro A _
    ext a
    obtain ⟨r, rfl⟩ := hbij.2 a
    simp [rowSet, hbij.1.eq_iff]
  · intro P _
    ext r
    simp [rowSet, hbij.1.eq_iff]
  · intro A _; rfl

end Tverberg6R
