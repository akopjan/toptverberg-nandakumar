module

public import Mathlib
public import RequestProject.Solution

@[expose] public section

/-!
# Sixfold Tverberg Counterexample and Convex Equipartition Obstruction (`Solution.lean`)

Arseniy Akopyan

Matches `Challenge.lean` via `comparator.json` without importing `Challenge.lean`:
* `AkopyanSixfold.tverberg_counterexample` (Theorem A):
  An almost six-embedding `Δ³⁵ → ℝ⁶`, proved via the height-table construction
  `Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension`.
* `AkopyanSixfold.convex_partition_counterexample` (Theorem B):
  In every dimension `d ≥ 24`, given `g₀ : Δ¹¹⁹ → ℝ²²` (Theorem C) and `5 * d` blocking
  markers `(p, eta)` for `eta`-central six-partitions, iterates join-padding (`d - 24` times)
  to produce an almost six-embedding `g : Δ^(5d-1) → ℝ^(d-2)`, transfers it via the
  Hausdorff-continuous inward-distance functional `inwardDist` to `d - 1` continuous body
  functionals `Phi`, and proves that no fair convex six-partition equalizes `Phi` for any
  `eta`-concentrated absolutely continuous measure (nor for a normalized Lebesgue ball witness).
* Additional results in `Solution.lean`:
  `join_almostSixEmbedding`, `tverberg_counterexample_ge_six` (`d ≥ 6`), `fivefold_tverberg_join`
  (`Δ¹⁷⁹ → ℝ³⁴`), `padded_tverberg_ge_36` (`d ≥ 36`), `twofold_seven_color_join`
  (`Δ⁴¹ → ℝ⁷` implies `Δ⁸³ → ℝ¹⁵`), `convex_partition_of_embedding_and_blocking`,
  `convex_partition_counterexample_ge_36` (`d ≥ 36`, without Theorem C), and
  `convex_partition_counterexample_ge_18` (`d ≥ 18`, conditional on `Δ⁸⁹ → ℝ¹⁶`
  and `5d` blocking markers).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Topology

namespace AkopyanSixfold

/-- The simplex on `n` vertices (dimension `n - 1`). -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1}

/-- The six points have pairwise disjoint barycentric supports. -/
def DisjointSupports {n : ℕ} (x : Fin 6 → (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j → ∀ v, x i v = 0 ∨ x j v = 0

/-- An almost six-embedding of the `(n - 1)`-simplex into `ℝ^d`:
continuity is required on the simplex, and no six points with pairwise disjoint
barycentric supports share the same image. -/
def IsAlmostSixEmbedding {n d : ℕ}
    (f : (Fin n → ℝ) → (Fin d → ℝ)) : Prop :=
  ContinuousOn f (simplex n) ∧
  ∀ x : Fin 6 → (Fin n → ℝ),
    (∀ i, x i ∈ simplex n) →
    DisjointSupports x →
    ∃ i, f (x i) ≠ f (x 0)

/-- **Theorem A**: Counterexample to the topological Tverberg conjecture for sixfold
intersections in `ℝ⁶` (`36` vertices, target dimension `6`). -/
theorem tverberg_counterexample :
    ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨f, hf_cont, hf_disj⟩ :=
    Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension
  exact ⟨f, hf_cont, hf_disj⟩

/-- Standard Euclidean space `ℝ^d`. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Nonempty compact convex bodies in `ℝ^d` endowed with the Hausdorff metric. -/
abbrev Body (d : ℕ) := ConvexBody (Ambient d)

/-- The closed unit ball in `ℝ^d`. -/
def unitBall (d : ℕ) : Set (Ambient d) :=
  Metric.closedBall (0 : Ambient d) 1

/-- A convex six-partition of the unit ball: six convex bodies with nonempty,
pairwise disjoint interiors whose union equals `unitBall d`. -/
def IsSixPartition {d : ℕ} (C : Fin 6 → Body d) : Prop :=
  unitBall d = (⋃ i, (C i : Set (Ambient d))) ∧
  (∀ i, (interior (C i : Set (Ambient d))).Nonempty) ∧
  ∀ i j, i ≠ j →
    Disjoint (interior (C i : Set (Ambient d)))
             (interior (C j : Set (Ambient d)))

/-- `p` and `eta ∈ (0, 1)` block central six-partitions if every six-partition
whose parts all meet the `eta`-ball contains some marker `p a` in the interior
of some part. -/
def IsBlocking {d m : ℕ} (p : Fin m → Ambient d) (eta : ℝ) : Prop :=
  0 < eta ∧ eta < 1 ∧
  ∀ C : Fin 6 → Body d, IsSixPartition C →
    (∀ i, ∃ x ∈ (C i : Set (Ambient d)), ‖x‖ ≤ eta) →
    ∃ i a, p a ∈ interior (C i : Set (Ambient d))

/-! ### Helper 1: Perspective continuity, binary joins, and join-padding -/

private lemma continuousOn_perspective {X : Type*} [TopologicalSpace X]
    {S : Set X} {n q : ℕ}
    {w : X → Fin n → ℝ}
    (hw_cont : ∀ v, ContinuousOn (fun x => w x v) S)
    (hw_nonneg : ∀ x ∈ S, ∀ v, 0 ≤ w x v)
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : ContinuousOn g (simplex n))
    (j : Fin q) :
    ContinuousOn
      (fun x =>
        let s := ∑ v, w x v
        if s = 0 then 0 else s * g (fun v => w x v / s) j)
      S := by
  let s : X → ℝ := fun x => ∑ v, w x v
  have hs_cont : ContinuousOn s S :=
    continuousOn_finsetSum _ fun v _ => hw_cont v
  have hs_nonneg : ∀ x ∈ S, 0 ≤ s x :=
    fun x hx => Finset.sum_nonneg fun v _ => hw_nonneg x hx v
  have h_simplex : ∀ x ∈ S, s x ≠ 0 → (fun v => w x v / s x) ∈ simplex n := by
    intro x hx hsx
    refine ⟨fun v => div_nonneg (hw_nonneg x hx v) (hs_nonneg x hx), ?_⟩
    rw [← Finset.sum_div]
    exact div_self hsx
  have hcompact : IsCompact (simplex n) := isCompact_stdSimplex ℝ (Fin n)
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hg
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hbound : ∀ y ∈ simplex n, |g y j| ≤ M := fun y hy =>
    (norm_le_pi_norm (g y) j).trans ((hM₀ y hy).trans (le_max_left M₀ 0))
  intro x₀ hx₀
  by_cases hs₀ : s x₀ = 0
  · change Filter.Tendsto
      (fun x => if s x = 0 then (0 : ℝ) else s x * g (fun v => w x v / s x) j)
      (𝓝[S] x₀) (𝓝 (if s x₀ = 0 then (0 : ℝ) else s x₀ * g (fun v => w x₀ v / s x₀) j))
    simp only [hs₀, ↓reduceIte]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (g := fun x => M * |s x|)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      by_cases hsx : s x = 0
      · simp [hsx]
      · simp only [hsx, ↓reduceIte, Real.norm_eq_abs, abs_mul]
        have hle := hbound _ (h_simplex x hx hsx)
        calc
          |s x| * |g (fun v => w x v / s x) j| ≤ |s x| * M := by gcongr
          _ = M * |s x| := mul_comm _ _
    · have htend : Filter.Tendsto (fun x => M * |s x|) (𝓝[S] x₀) (𝓝 (M * |s x₀|)) :=
        (continuous_const.continuousWithinAt.mul
          (continuous_abs.continuousAt.comp_continuousWithinAt (hs_cont x₀ hx₀))).tendsto
      simpa [hs₀] using htend
  · let yMap : X → Fin n → ℝ := fun x v => w x v / s x
    have hyMap_tend : Filter.Tendsto yMap (𝓝[S] x₀) (𝓝 (yMap x₀)) :=
      tendsto_pi_nhds.mpr fun v =>
        ((hw_cont v x₀ hx₀).div (hs_cont x₀ hx₀) hs₀).tendsto
    have hsnz : {x : X | s x ≠ 0} ∈ 𝓝[S] x₀ :=
      (hs_cont x₀ hx₀).tendsto (isOpen_ne.mem_nhds hs₀)
    have h_maps : Filter.Tendsto yMap (𝓝[S] x₀) (𝓝[simplex n] (yMap x₀)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hyMap_tend, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hsnz] with x hx hsx
      exact h_simplex x hx hsx
    have hg_at : ContinuousWithinAt (fun y => g y j) (simplex n) (yMap x₀) :=
      (continuous_apply j).continuousAt.comp_continuousWithinAt
        (hg (yMap x₀) (h_simplex x₀ hx₀ hs₀))
    have h_prod : ContinuousWithinAt (fun x => s x * g (yMap x) j) S x₀ :=
      (hs_cont x₀ hx₀).mul (hg_at.tendsto.comp h_maps)
    refine h_prod.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hsnz] with x hx
      simp [s, hx, yMap]
    · simp [s, hs₀, yMap]

/-- The binary join `g₁ * g₂ : Δ^(m+n-1) → ℝ^(p+q+1)` of two almost six-embeddings is an
almost six-embedding. -/
theorem join_almostSixEmbedding {m n p q : ℕ}
    {g₁ : (Fin m → ℝ) → (Fin p → ℝ)} {g₂ : (Fin n → ℝ) → (Fin q → ℝ)}
    (hg₁ : IsAlmostSixEmbedding g₁) (hg₂ : IsAlmostSixEmbedding g₂) :
    ∃ f : (Fin (m + n) → ℝ) → (Fin (p + q + 1) → ℝ),
      IsAlmostSixEmbedding f := by
  let w₁ : (Fin (m + n) → ℝ) → Fin m → ℝ := fun x v => x (Fin.castAdd n v)
  let w₂ : (Fin (m + n) → ℝ) → Fin n → ℝ := fun x w => x (Fin.natAdd m w)
  let t : (Fin (m + n) → ℝ) → ℝ := fun x => ∑ v : Fin m, w₁ x v
  let s : (Fin (m + n) → ℝ) → ℝ := fun x => ∑ w : Fin n, w₂ x w
  let f : (Fin (m + n) → ℝ) → (Fin (p + q + 1) → ℝ) := fun x k =>
    if _hk0 : k = 0 then t x
    else if hkp : k.1 - 1 < p then
      if t x = 0 then 0 else t x * g₁ (fun v => w₁ x v / t x) ⟨k.1 - 1, hkp⟩
    else
      if s x = 0 then 0 else s x * g₂ (fun w => w₂ x w / s x) ⟨k.1 - 1 - p, by have := k.isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · refine continuousOn_pi.mpr fun k => ?_
    by_cases hk0 : k = 0
    · have hfun : (fun x => f x k) = t := funext fun x => by simp [f, hk0]
      rw [hfun]
      exact (continuous_finsetSum Finset.univ fun v _ =>
        continuous_apply (Fin.castAdd n v)).continuousOn
    · by_cases hkp : k.1 - 1 < p
      · have hfun :
            (fun x => f x k) = fun x =>
              let t' := ∑ v, w₁ x v
              if t' = 0 then 0 else t' * g₁ (fun v => w₁ x v / t') ⟨k.1 - 1, hkp⟩ :=
          funext fun x => by simp [f, hk0, hkp, t]
        rw [hfun]
        exact continuousOn_perspective (fun v => (continuous_apply _).continuousOn)
          (fun _ hx v => hx.1 _) hg₁.1 ⟨k.1 - 1, hkp⟩
      · have hfun :
            (fun x => f x k) = fun x =>
              let s' := ∑ w, w₂ x w
              if s' = 0 then 0 else s' * g₂ (fun w => w₂ x w / s') ⟨k.1 - 1 - p, by have := k.isLt; omega⟩ :=
          funext fun x => by simp [f, hk0, hkp, s]
        rw [hfun]
        exact continuousOn_perspective (fun w => (continuous_apply _).continuousOn)
          (fun _ hx w => hx.1 _) hg₂.1 ⟨k.1 - 1 - p, by have := k.isLt; omega⟩
  · intro x hx hdisj
    by_contra h_all
    push Not at h_all
    have ht_eq : ∀ i, t (x i) = t (x 0) := fun i => by
      have h0 := congrFun (h_all i) 0
      simpa [f] using h0
    have hts_sum : ∀ i, t (x i) + s (x i) = 1 := fun i => by
      have hsum := (hx i).2
      rw [Fin.sum_univ_add] at hsum
      exact hsum
    have hs_eq : ∀ i, s (x i) = s (x 0) := fun i => by
      linarith [hts_sum i, hts_sum 0, ht_eq i]
    by_cases ht0 : t (x 0) = 0
    · have hs0 : s (x 0) = 1 := by linarith [hts_sum 0, ht0]
      have hsi_ne : ∀ i, s (x i) ≠ 0 := fun i => by
        rw [hs_eq i, hs0]
        norm_num
      have hsi_nonneg : ∀ i, 0 ≤ s (x i) := fun i =>
        Finset.sum_nonneg fun w _ => (hx i).1 _
      let y : Fin 6 → Fin n → ℝ := fun i w => w₂ (x i) w / s (x i)
      have hy_mem : ∀ i, y i ∈ simplex n := fun i =>
        ⟨fun w => div_nonneg ((hx i).1 _) (hsi_nonneg i),
          by rw [← Finset.sum_div]; exact div_self (hsi_ne i)⟩
      have hy_disj : DisjointSupports y := fun i j hij w => by
        rcases hdisj i j hij (Fin.natAdd m w) with hi0 | hj0
        · left; simp [y, w₂, hi0]
        · right; simp [y, w₂, hj0]
      obtain ⟨i, hi_ne⟩ := hg₂.2 y hy_mem hy_disj
      apply hi_ne
      funext j
      let k : Fin (p + q + 1) := ⟨1 + p + j.1, by omega⟩
      have hk0 : k ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [k] at hv
      have hkp : ¬ k.1 - 1 < p := by simp [k]; omega
      have hksub : (⟨k.1 - 1 - p, by have := k.isLt; omega⟩ : Fin q) = j := by
        ext; simp [k]; omega
      have hcon := congrFun (h_all i) k
      simp only [f, hk0, ↓reduceDIte, hkp, hs_eq i, hs0, one_ne_zero, ↓reduceIte, hksub] at hcon
      simpa [y, hs_eq i, hs0] using hcon
    · have hti_ne : ∀ i, t (x i) ≠ 0 := fun i => (ht_eq i).symm ▸ ht0
      have hti_nonneg : ∀ i, 0 ≤ t (x i) := fun i =>
        Finset.sum_nonneg fun v _ => (hx i).1 _
      let y : Fin 6 → Fin m → ℝ := fun i v => w₁ (x i) v / t (x i)
      have hy_mem : ∀ i, y i ∈ simplex m := fun i =>
        ⟨fun v => div_nonneg ((hx i).1 _) (hti_nonneg i),
          by rw [← Finset.sum_div]; exact div_self (hti_ne i)⟩
      have hy_disj : DisjointSupports y := fun i j hij v => by
        rcases hdisj i j hij (Fin.castAdd n v) with hi0 | hj0
        · left; simp [y, w₁, hi0]
        · right; simp [y, w₁, hj0]
      obtain ⟨i, hi_ne⟩ := hg₁.2 y hy_mem hy_disj
      apply hi_ne
      funext j
      let k : Fin (p + q + 1) := ⟨1 + j.1, by omega⟩
      have hk0 : k ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [k] at hv
      have hkp : k.1 - 1 < p := by simp [k]
      have hksub : (⟨k.1 - 1, hkp⟩ : Fin p) = j := by
        ext; simp [k]
      have hcon := congrFun (h_all i) k
      simp only [f, hk0, ↓reduceDIte, hkp, ht_eq i, ht0, ↓reduceIte, hksub] at hcon
      exact mul_left_cancel₀ ht0 (by simpa [y, ht_eq i] using hcon)

private lemma emptyFive_almostSixEmbedding :
    IsAlmostSixEmbedding (fun (_ : Fin 5 → ℝ) => (Fin.elim0 : Fin 0 → ℝ)) := by
  refine ⟨continuousOn_const, fun x hx hdisj => ?_⟩
  exfalso
  have hex : ∀ i : Fin 6, ∃ v : Fin 5, x i v ≠ 0 := fun i => by
    by_contra hzero
    push Not at hzero
    have hsum0 : (∑ v : Fin 5, x i v) = 0 := Finset.sum_eq_zero fun v _ => hzero v
    linarith [(hx i).2]
  choose v hv using hex
  obtain ⟨i, j, hij, hvij⟩ := Fintype.exists_ne_map_eq_of_card_lt v (by simp)
  rcases hdisj i j hij (v i) with hi0 | hj0
  · exact hv i hi0
  · rw [hvij] at hj0
    exact hv j hj0

/-- Join-padding preserves almost six-embeddings (adding 5 vertices and 1 target coordinate). -/
private lemma padding_almostSixEmbedding {n q : ℕ}
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : IsAlmostSixEmbedding g) :
    ∃ f : (Fin (n + 5) → ℝ) → (Fin (q + 1) → ℝ),
      IsAlmostSixEmbedding f := by
  simpa using join_almostSixEmbedding hg emptyFive_almostSixEmbedding

private lemma reindex_almostSixEmbedding {n m q r : ℕ} (hn : n = m) (hq : q = r)
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : IsAlmostSixEmbedding g) :
    ∃ f : (Fin m → ℝ) → (Fin r → ℝ), IsAlmostSixEmbedding f := by
  let castDom : (Fin m → ℝ) → (Fin n → ℝ) := fun x v => x (Fin.cast hn v)
  let f : (Fin m → ℝ) → (Fin r → ℝ) := fun x j => g (castDom x) (Fin.cast hq.symm j)
  have hcastDom_mem : ∀ x ∈ simplex m, castDom x ∈ simplex n := fun x hx => by
    refine ⟨fun v => hx.1 _, ?_⟩
    calc
      ∑ v : Fin n, x (Fin.cast hn v) = ∑ w : Fin m, x w :=
        Fintype.sum_equiv (finCongr hn) (fun v => x (Fin.cast hn v)) x (fun _ => rfl)
      _ = 1 := hx.2
  refine ⟨f, ?_, ?_⟩
  · have hcast_cont : Continuous castDom := continuous_pi fun v => continuous_apply _
    have hg_comp : ContinuousOn (fun x => g (castDom x)) (simplex m) :=
      hg.1.comp hcast_cont.continuousOn hcastDom_mem
    refine continuousOn_pi.mpr fun j => ?_
    exact (continuous_apply (Fin.cast hq.symm j)).continuousOn.comp hg_comp (fun _ _ => Set.mem_univ _)
  · intro x hx hdisj
    have hdisj' : DisjointSupports (fun i => castDom (x i)) :=
      fun i j hij v => hdisj i j hij (Fin.cast hn v)
    obtain ⟨i, hi⟩ := hg.2 (fun i => castDom (x i)) (fun i => hcastDom_mem (x i) (hx i)) hdisj'
    refine ⟨i, fun heq => hi ?_⟩
    funext j
    have hcon := congrFun heq (Fin.cast hq j)
    simpa [f] using hcon

private lemma iterated_padding_from {n₀ q₀ : ℕ} (k : ℕ)
    {g₀ : (Fin n₀ → ℝ) → (Fin q₀ → ℝ)} (hg₀ : IsAlmostSixEmbedding g₀) :
    ∃ f : (Fin (n₀ + 5 * k) → ℝ) → (Fin (q₀ + k) → ℝ),
      IsAlmostSixEmbedding f := by
  induction k with
  | zero =>
    simpa using ⟨g₀, hg₀⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨f, hf⟩ := padding_almostSixEmbedding hg
    exact reindex_almostSixEmbedding (by omega : n₀ + 5 * k + 5 = n₀ + 5 * (k + 1))
      (by omega : q₀ + k + 1 = q₀ + (k + 1)) hf

/-- **Best unconditional Tverberg counterexample for `r = 6`**: in every dimension `d ≥ 6`,
there is an almost six-embedding `Δ^(5d+5) → ℝ^d` (`5d + 6` vertices). -/
theorem tverberg_counterexample_ge_six (d : ℕ) (hd : 6 ≤ d) :
    ∃ f : (Fin (5 * d + 6) → ℝ) → (Fin d → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨g₀, hg₀⟩ := tverberg_counterexample
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 6) hg₀
  exact reindex_almostSixEmbedding (by omega : 36 + 5 * (d - 6) = 5 * d + 6)
    (by omega : 6 + (d - 6) = d) hg

/-- **Fivefold join of Theorem A (no `[AKS]` needed)**: an unconditional almost six-embedding
`Δ¹⁷⁹ → ℝ³⁴` (`180 = 5 * 36` vertices, `34 = 36 - 2` target coordinates). -/
theorem fivefold_tverberg_join :
    ∃ f : (Fin 180 → ℝ) → (Fin 34 → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨f₁, hf₁⟩ := tverberg_counterexample
  obtain ⟨f₂, hf₂⟩ := join_almostSixEmbedding hf₁ hf₁
  obtain ⟨f₃, hf₃⟩ := join_almostSixEmbedding hf₂ hf₁
  obtain ⟨f₄, hf₄⟩ := join_almostSixEmbedding hf₃ hf₁
  exact join_almostSixEmbedding hf₄ hf₁

/-- **Padded fivefold join (`d ≥ 36`, no `[AKS]`)**: for every `d ≥ 36`, there exists an
unconditional almost six-embedding `Δ^(5d-1) → ℝ^(d-2)` (`5d` vertices). -/
theorem padded_tverberg_ge_36 (d : ℕ) (hd : 36 ≤ d) :
    ∃ g : (Fin (5 * d) → ℝ) → (Fin (d - 2) → ℝ),
      IsAlmostSixEmbedding g := by
  obtain ⟨g₀, hg₀⟩ := fivefold_tverberg_join
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 36) hg₀
  exact reindex_almostSixEmbedding (by omega : 180 + 5 * (d - 36) = 5 * d)
    (by omega : 34 + (d - 36) = d - 2) hg

/-- **Twofold seven-color join**: given an almost six-embedding `f₇ : Δ⁴¹ → ℝ⁷`
(Section 2.3 of the research report), its self-join gives an almost six-embedding
`Δ⁸³ → ℝ¹⁵` (`84` vertices). -/
theorem twofold_seven_color_join
    {f₇ : (Fin 42 → ℝ) → (Fin 7 → ℝ)} (hf₇ : IsAlmostSixEmbedding f₇) :
    ∃ f : (Fin 84 → ℝ) → (Fin 15 → ℝ),
      IsAlmostSixEmbedding f := by
  simpa using join_almostSixEmbedding hf₇ hf₇

/-! ### Helper 2: Hausdorff-continuous inward distance (Lemma 5.3) -/

/-- Inward distance of a point `p` to the boundary/complement of a convex body `C`. -/
def inwardDist {d : ℕ} (p : Ambient d) (C : Body d) : ℝ :=
  Metric.infDist p (C : Set (Ambient d))ᶜ

private lemma body_compl_nonempty {d : ℕ} (hd : 0 < d) (C : Body d) :
    (C : Set (Ambient d))ᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := C.isCompact.isBounded.subset_closedBall (0 : Ambient d)
  let e0 : Ambient d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have he0 : ‖e0‖ = 1 :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).norm_eq_one ⟨0, hd⟩
  let x₀ : Ambient d := (max R 0 + 1) • e0
  refine ⟨x₀, fun hx₀ => ?_⟩
  have hle : dist x₀ 0 ≤ R := hR hx₀
  have hx₀_norm : ‖x₀‖ = max R 0 + 1 := by
    rw [norm_smul, he0, mul_one, Real.norm_of_nonneg (by positivity)]
  rw [dist_zero_right, hx₀_norm] at hle
  linarith [le_max_left R 0]

private lemma inwardDist_pos_iff {d : ℕ} (hd : 0 < d) (p : Ambient d) (C : Body d) :
    0 < inwardDist p C ↔ p ∈ interior (C : Set (Ambient d)) := by
  have hne : (C : Set (Ambient d))ᶜ.Nonempty := body_compl_nonempty hd C
  unfold inwardDist
  rw [← Metric.infDist_pos_iff_notMem_closure hne]
  rw [interior_eq_compl_closure_compl]
  simp

private lemma inwardDist_le {d : ℕ} (hd : 0 < d) (p : Ambient d) (C D : Body d) :
    inwardDist p D ≤ inwardDist p C + dist C D := by
  have hneC : (C : Set (Ambient d))ᶜ.Nonempty := body_compl_nonempty hd C
  suffices h : inwardDist p D - dist C D ≤ inwardDist p C by linarith
  refine (Metric.le_infDist hneC).2 fun y hyC => ?_
  have hy_compl : y ∉ (C : Set (Ambient d)) := hyC
  obtain ⟨f, s, hfC, hfy⟩ :=
    geometric_hahn_banach_closed_point C.convex C.isClosed hy_compl
  let v : Ambient d := (InnerProductSpace.toDual ℝ (Ambient d)).symm f
  have hv_ne : v ≠ 0 := by
    intro hv0
    obtain ⟨x₀, hx₀⟩ := C.nonempty
    have hf_zero : f = 0 := by
      have hmap := congrArg (InnerProductSpace.toDual ℝ (Ambient d)) hv0
      simpa [v] using hmap
    have h1 := hfC x₀ hx₀
    simp only [hf_zero, zero_apply] at h1 hfy
    linarith
  let u : Ambient d := (‖v‖)⁻¹ • v
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv_ne)]
  have hu_sep : ∀ x ∈ (C : Set (Ambient d)), ⟪u, x⟫_ℝ < ⟪u, y⟫_ℝ := by
    intro x hx
    have hnorm_pos : 0 < (‖v‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hv_ne)
    have hfx_lt_fy : f x < f y := (hfC x hx).trans hfy
    have hvx : ⟪v, x⟫_ℝ = f x := InnerProductSpace.toDual_symm_apply
    have hvy : ⟪v, y⟫_ℝ = f y := InnerProductSpace.toDual_symm_apply
    calc
      ⟪u, x⟫_ℝ = (‖v‖)⁻¹ * ⟪v, x⟫_ℝ := by simp [u, real_inner_smul_left]
      _ = (‖v‖)⁻¹ * f x := by rw [hvx]
      _ < (‖v‖)⁻¹ * f y := mul_lt_mul_of_pos_left hfx_lt_fy hnorm_pos
      _ = (‖v‖)⁻¹ * ⟪v, y⟫_ℝ := by rw [hvy]
      _ = ⟪u, y⟫_ℝ := by simp [u, real_inner_smul_left]
  suffices hdelta : ∀ δ : ℝ, 0 < δ → inwardDist p D ≤ dist p y + (dist C D + δ) by
    have h_le : inwardDist p D - dist C D ≤ dist p y := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      linarith [hdelta δ hδ]
    exact h_le
  intro δ hδ
  let z : Ambient d := y + (dist C D + δ) • u
  have hzD : z ∈ (D : Set (Ambient d))ᶜ := by
    intro hz_mem
    have hhaus : Metric.hausdorffDist (C : Set (Ambient d)) (D : Set (Ambient d)) < dist C D + δ := by
      rw [ConvexBody.hausdorffDist_coe]
      linarith
    obtain ⟨x, hxC, hxz⟩ :=
      Metric.exists_dist_lt_of_hausdorffDist_lt' hz_mem hhaus ConvexBody.hausdorffEDist_ne_top
    have h_upper : ⟪u, z - x⟫_ℝ < dist C D + δ := by
      have hcs : ⟪u, z - x⟫_ℝ ≤ ‖u‖ * ‖z - x‖ := real_inner_le_norm u (z - x)
      rw [hu_norm, one_mul, ← dist_eq_norm, dist_comm] at hcs
      exact hcs.trans_lt hxz
    have h_lower : dist C D + δ < ⟪u, z - x⟫_ℝ := by
      have hzx_eq : z - x = (y - x) + (dist C D + δ) • u := by
        simp [z]; abel
      have hu_self : ⟪u, u⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, hu_norm, one_pow]
      rw [hzx_eq, inner_add_right, inner_smul_right, hu_self, mul_one, inner_sub_right]
      linarith [hu_sep x hxC]
    linarith
  have hdist_yz : dist y z = dist C D + δ := by
    rw [dist_eq_norm, show y - z = -((dist C D + δ) • u) by simp [z], norm_neg, norm_smul,
      hu_norm, mul_one, Real.norm_of_nonneg (add_nonneg dist_nonneg hδ.le)]
  have hinf : inwardDist p D ≤ dist p z := Metric.infDist_le_dist_of_mem hzD
  exact hinf.trans ((dist_triangle p y z).trans (by rw [hdist_yz]))

private lemma continuous_inwardDist {d : ℕ} (hd : 0 < d) (p : Ambient d) :
    Continuous (inwardDist p : Body d → ℝ) :=
  (LipschitzWith.of_le_add fun C D => by
    rw [dist_comm]
    exact inwardDist_le hd p D C).continuous

/-! ### Helper 3: Fair partitions under concentrated measures & Lebesgue restriction -/

private lemma fair_meets_eta_ball {d : ℕ} {eta : ℝ} (heta : eta < 1)
    {mu : Measure (Ambient d)}
    (_hpos : 0 < mu (unitBall d)) (htop : mu (unitBall d) < ⊤)
    (hconc : 5 * mu (unitBall d) < 6 * mu (Metric.closedBall (0 : Ambient d) eta))
    {C : Fin 6 → Body d} (hC : IsSixPartition C)
    (hfair : ∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) :
    ∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty := by
  intro i
  by_contra h_empty
  have h_disj : Disjoint (C i : Set (Ambient d)) (Metric.closedBall (0 : Ambient d) eta) :=
    Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h_empty)
  have h_sub_C : (C i : Set (Ambient d)) ⊆ unitBall d := by
    rw [hC.1]
    exact Set.subset_iUnion (fun j => (C j : Set (Ambient d))) i
  have h_sub_eta : Metric.closedBall (0 : Ambient d) eta ⊆ unitBall d :=
    Metric.closedBall_subset_closedBall heta.le
  have h_union_le :
      mu (C i : Set (Ambient d)) + mu (Metric.closedBall (0 : Ambient d) eta) ≤
        mu (unitBall d) := by
    rw [← measure_union h_disj Metric.isClosed_closedBall.measurableSet]
    exact measure_mono (Set.union_subset h_sub_C h_sub_eta)
  rw [hfair i] at h_union_le
  have hB_ne_top : mu (unitBall d) ≠ ⊤ := htop.ne
  have hE_ne_top : mu (Metric.closedBall (0 : Ambient d) eta) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono h_sub_eta) htop).ne
  have hconc_real :
      5 * (mu (unitBall d)).toReal < 6 * (mu (Metric.closedBall (0 : Ambient d) eta)).toReal := by
    have h6E_ne_top : (6 : ENNReal) * mu (Metric.closedBall (0 : Ambient d) eta) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hE_ne_top
    have h5B_ne_top : (5 : ENNReal) * mu (unitBall d) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hB_ne_top
    have hlt := (ENNReal.toReal_lt_toReal h5B_ne_top h6E_ne_top).mpr hconc
    simpa [ENNReal.toReal_mul] using hlt
  have hsum_real :
      (mu (unitBall d)).toReal / 6 + (mu (Metric.closedBall (0 : Ambient d) eta)).toReal ≤
        (mu (unitBall d)).toReal := by
    have h_div_ne_top : mu (unitBall d) / 6 ≠ ⊤ :=
      ENNReal.div_ne_top hB_ne_top (by norm_num)
    have hle := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨h_div_ne_top, hE_ne_top⟩)
      hB_ne_top).mpr h_union_le
    simpa [ENNReal.toReal_add h_div_ne_top hE_ne_top, ENNReal.toReal_div] using hle
  linarith

private lemma normalized_ball_measure_props {d : ℕ} {eta : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    let S : Set (Ambient d) := Metric.closedBall (0 : Ambient d) eta
    let mu : Measure (Ambient d) := (volume S)⁻¹ • volume.restrict S
    IsProbabilityMeasure mu ∧
    mu.AbsolutelyContinuous (volume : Measure (Ambient d)) ∧
    0 < mu (unitBall d) ∧
    mu (unitBall d) < ⊤ ∧
    5 * mu (unitBall d) < 6 * mu S := by
  intro S mu
  have hS_pos : 0 < volume S :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self heta0⟩)
      (measure_mono Metric.ball_subset_closedBall)
  have hS_top : volume S < ⊤ := (isCompact_closedBall (0 : Ambient d) eta).measure_lt_top
  have hS_ne_zero : volume S ≠ 0 := hS_pos.ne'
  have hS_ne_top : volume S ≠ ⊤ := hS_top.ne
  have hmu_univ : mu Set.univ = 1 := by
    simp [mu, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hS_ne_zero hS_ne_top]
  have hmu_prob : IsProbabilityMeasure mu := ⟨hmu_univ⟩
  have hmu_ac : mu.AbsolutelyContinuous volume := fun s hs => by
    have h0 : volume.restrict S s = 0 :=
      nonpos_iff_eq_zero.mp ((Measure.restrict_le_self s).trans hs.le)
    simp [mu, Measure.smul_apply, h0]
  have hmu_S : mu S = 1 := by
    simp [mu, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self,
      ENNReal.inv_mul_cancel hS_ne_zero hS_ne_top]
  have hS_sub_ball : S ⊆ unitBall d := Metric.closedBall_subset_closedBall heta1.le
  have hmu_ball : mu (unitBall d) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hmu_univ]
      exact measure_mono (Set.subset_univ _)
    · rw [← hmu_S]
      exact measure_mono hS_sub_ball
  refine ⟨hmu_prob, hmu_ac, ?_, ?_, ?_⟩
  · simp [hmu_ball]
  · simp [hmu_ball]
  · rw [hmu_ball, hmu_S]
    norm_num

/-- **General convex equipartition transfer**: given any almost six-embedding
`g : Δ^(m-1) → ℝ^(d-2)` and `m` blocking markers `(p, eta)` in dimension `d ≥ 2`,
constructs `d - 1` continuous functionals `Phi` and an absolutely continuous
probability measure `mu` (and in fact works uniformly for every `eta`-concentrated
absolutely continuous measure) such that no fair convex six-partition equalizes `Phi`. -/
theorem convex_partition_of_embedding_and_blocking {d m : ℕ} (hd : 2 ≤ d)
    {g : (Fin m → ℝ) → (Fin (d - 2) → ℝ)} (hg : IsAlmostSixEmbedding g)
    {p : Fin m → Ambient d} {eta : ℝ} (hp : IsBlocking p eta) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  have hd_pos : 0 < d := by omega
  let w : Body d → Fin m → ℝ := fun C a => inwardDist (p a) C
  let s : Body d → ℝ := fun C => ∑ a, w C a
  let Phi : Body d → (Fin (d - 1) → ℝ) := fun C k =>
    if _hk : k.1 = 0 then s C
    else
      if s C = 0 then 0
      else s C * g (fun a => w C a / s C) ⟨k.1 - 1, by have := k.isLt; omega⟩
  have hw_nonneg : ∀ C a, 0 ≤ w C a := fun _ _ => Metric.infDist_nonneg
  have hs_nonneg : ∀ C, 0 ≤ s C := fun C => Finset.sum_nonneg fun a _ => hw_nonneg C a
  have hs_cont : Continuous s :=
    continuous_finsetSum _ fun a _ => continuous_inwardDist hd_pos (p a)
  have h_simplex_of_pos : ∀ C, s C ≠ 0 → (fun a => w C a / s C) ∈ simplex m := by
    intro C hsC
    refine ⟨fun a => div_nonneg (hw_nonneg C a) (hs_nonneg C), ?_⟩
    rw [← Finset.sum_div]
    exact div_self hsC
  have hPhi_cont : Continuous Phi := by
    refine continuous_pi fun k => ?_
    by_cases hk : k.1 = 0
    · simpa [Phi, hk] using hs_cont
    · have hfun :
          (fun C : Body d => Phi C k) = fun C =>
            let s' := ∑ a, w C a
            if s' = 0 then 0 else s' * g (fun a => w C a / s') ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
        funext fun C => by simp [Phi, hk, s]
      rw [hfun]
      exact continuousOn_univ.mp <| continuousOn_perspective
        (fun a => (continuous_inwardDist hd_pos (p a)).continuousOn)
        (fun C _ a => hw_nonneg C a) hg.1 ⟨k.1 - 1, by have := k.isLt; omega⟩
  have hPhi_obstruct :
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
    intro C hC hmeet
    by_contra h_all
    push Not at h_all
    have hs_eq : ∀ i, s (C i) = s (C 0) := fun i => by
      have h0 := congrFun (h_all i) ⟨0, by omega⟩
      simpa [Phi] using h0
    by_cases hs0 : s (C 0) = 0
    · have hno_int : ∀ i a, p a ∉ interior (C i : Set (Ambient d)) := fun i a hmem => by
        have hpos_w : 0 < w (C i) a := (inwardDist_pos_iff hd_pos (p a) (C i)).mpr hmem
        have hsum0 : s (C i) = 0 := (hs_eq i).trans hs0
        have hw0 : w (C i) a = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hw_nonneg (C i) b) |>.mp hsum0 a
            (Finset.mem_univ a)
        linarith
      obtain ⟨i, a, ha⟩ := hp.2.2 C hC fun i => by
        obtain ⟨y, hyC, hyeta⟩ := hmeet i
        exact ⟨y, hyC, by simpa [Metric.mem_closedBall, dist_zero_right] using hyeta⟩
      exact hno_int i a ha
    · have hsi_ne : ∀ i, s (C i) ≠ 0 := fun i => (hs_eq i).symm ▸ hs0
      let x : Fin 6 → Fin m → ℝ := fun i a => w (C i) a / s (C i)
      have hx_mem : ∀ i, x i ∈ simplex m :=
        fun i => h_simplex_of_pos (C i) (hsi_ne i)
      have hx_disj : DisjointSupports x := by
        intro i j hij a
        by_contra h_both
        push Not at h_both
        have hwi : 0 < w (C i) a := by
          have hle := hw_nonneg (C i) a
          by_contra hle0
          have heq0 : w (C i) a = 0 := le_antisymm (not_lt.mp hle0) hle
          exact h_both.1 (by simp [x, heq0])
        have hwj : 0 < w (C j) a := by
          have hle := hw_nonneg (C j) a
          by_contra hle0
          have heq0 : w (C j) a = 0 := le_antisymm (not_lt.mp hle0) hle
          exact h_both.2 (by simp [x, heq0])
        have hi_int : p a ∈ interior (C i : Set (Ambient d)) :=
          (inwardDist_pos_iff hd_pos (p a) (C i)).mp hwi
        have hj_int : p a ∈ interior (C j : Set (Ambient d)) :=
          (inwardDist_pos_iff hd_pos (p a) (C j)).mp hwj
        exact Set.disjoint_left.mp (hC.2.2 i j hij) hi_int hj_int
      obtain ⟨i, hi_ne⟩ := hg.2 x hx_mem hx_disj
      apply hi_ne
      funext j
      let k : Fin (d - 1) := ⟨j.1 + 1, by have := j.isLt; omega⟩
      have hk0 : k.1 ≠ 0 := by simp [k]
      have hcon := congrFun (h_all i) k
      simp only [Phi, hk0, ↓reduceDIte, hs_eq i, hs0, ↓reduceIte, k] at hcon
      have hksub : (⟨j.1 + 1 - 1, by have := j.isLt; omega⟩ : Fin (d - 2)) = j := by
        ext; simp
      rw [hksub] at hcon
      have hmul : s (C 0) * g (x i) j = s (C 0) * g (x 0) j := by
        simpa [x, hs_eq i] using hcon
      exact mul_left_cancel₀ hs0 hmul
  have h_unif :
      ∀ mu : Measure (Ambient d),
        mu.AbsolutelyContinuous (volume : Measure (Ambient d)) →
        0 < mu (unitBall d) →
        mu (unitBall d) < ⊤ →
        5 * mu (unitBall d) < 6 * mu (Metric.closedBall (0 : Ambient d) eta) →
        ∀ C : Fin 6 → Body d,
          IsSixPartition C →
          (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
          ∃ i, Phi (C i) ≠ Phi (C 0) := by
    intro mu _ hpos htop hconc C hC hfair
    exact hPhi_obstruct C hC (fair_meets_eta_ball hp.2.1 hpos htop hconc hC hfair)
  obtain ⟨hprob, hac, hpos, htop, hconc⟩ :=
    normalized_ball_measure_props (d := d) hp.1 hp.2.1
  exact ⟨Phi, _, hPhi_cont, hprob, hac,
    fun C hC hfair => h_unif _ hac hpos htop hconc C hC hfair⟩

private theorem convex_partition_from_base {d₀ d : ℕ} (hd₀ : 2 ≤ d₀) (hd : d₀ ≤ d)
    {g₀ : (Fin (5 * d₀) → ℝ) → (Fin (d₀ - 2) → ℝ)} (hg₀ : IsAlmostSixEmbedding g₀)
    {p : Fin (5 * d) → Ambient d} {eta : ℝ} (hp : IsBlocking p eta) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₁, hg₁⟩ := iterated_padding_from (d - d₀) hg₀
  obtain ⟨g, hg⟩ := reindex_almostSixEmbedding (by omega : 5 * d₀ + 5 * (d - d₀) = 5 * d)
    (by omega : (d₀ - 2) + (d - d₀) = d - 2) hg₁
  exact convex_partition_of_embedding_and_blocking (by omega) hg hp

/-- **Theorem B**: In every dimension `d ≥ 24`, given an almost six-embedding
`g₀ : Δ¹¹⁹ → ℝ²²` (Theorem C of the paper) and `5 * d` blocking markers `(p, eta)`,
there exist `d - 1` continuous functionals on convex bodies and an absolutely continuous
probability measure such that no convex six-partition of the unit ball into six parts
of equal measure equalizes all these functionals. -/
theorem convex_partition_counterexample (d : ℕ) (hd : 24 ≤ d)
    (g₀ : (Fin 120 → ℝ) → (Fin 22 → ℝ)) (hg₀ : IsAlmostSixEmbedding g₀)
    (p : Fin (5 * d) → Ambient d) (eta : ℝ) (hp : IsBlocking p eta) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) :=
  convex_partition_from_base (by norm_num : 2 ≤ 24) hd hg₀ hp

/-- **Conditional `d ≥ 18` reduction (Section 3.1–3.3 of the research report)**: in every
dimension `d ≥ 18`, given an almost six-embedding `g₀ : Δ⁸⁹ → ℝ¹⁶` and `5 * d` blocking
markers `(p, eta)`, join-padding `d - 18` times and inward-distance transfer yield the
same obstruction. -/
theorem convex_partition_counterexample_ge_18 (d : ℕ) (hd : 18 ≤ d)
    (g₀ : (Fin 90 → ℝ) → (Fin 16 → ℝ)) (hg₀ : IsAlmostSixEmbedding g₀)
    (p : Fin (5 * d) → Ambient d) (eta : ℝ) (hp : IsBlocking p eta) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) :=
  convex_partition_from_base (by norm_num : 2 ≤ 18) hd hg₀ hp

/-- **`[AKS]`-free Convex Equipartition Transfer (`d ≥ 36`)**: In every dimension `d ≥ 36`,
using the unconditional fivefold join of Theorem A (`fivefold_tverberg_join`), `5 * d`
blocking markers suffice without any external almost-six-embedding assumption. -/
theorem convex_partition_counterexample_ge_36 (d : ℕ) (hd : 36 ≤ d)
    (p : Fin (5 * d) → Ambient d) (eta : ℝ) (hp : IsBlocking p eta) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg₀⟩ := fivefold_tverberg_join
  exact convex_partition_from_base (by norm_num : 2 ≤ 36) hd hg₀ hp

end AkopyanSixfold
end
