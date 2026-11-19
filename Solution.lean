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
  Unconditionally in every dimension `d ≥ 288`, proves the existence of `5 * d + 36`
  central blocking markers (`exists_isBlocking`, via separating normals, normal rank ≤ 5
  [Lemma 4.2], Gaussian elimination to RREF, and measure-zero polynomial parametrization),
  derives `eta` via Blaschke compactness (`blaschke_isCompact_subsets_unitBall` /
  `exists_eta_of_isBlocking`, Lemma 5.2), constructs an unconditional almost six-embedding
  `Δ^(5d+35) → ℝ^(d-2)` by a 41-fold join of Theorem A plus join-padding (`kfold_tverberg_join`
  / `padded_tverberg_ge_288`), and transfers it via `inwardDist` to `d - 1` continuous body
  functionals `Phi` and an absolutely continuous probability measure `mu` without equalizing
  convex six-partitions.
* Additional results in `Solution.lean`:
  `join_almostSixEmbedding`, `tverberg_counterexample_ge_six` (`d ≥ 6`), `fivefold_tverberg_join`
  (`Δ¹⁷⁹ → ℝ³⁴`), `padded_tverberg_ge_36` (`d ≥ 36`), `twofold_seven_color_join`
  (`Δ⁴¹ → ℝ⁷` implies `Δ⁸³ → ℝ¹⁵`), `convex_partition_of_embedding_and_blocking`,
  `convex_partition_counterexample_ge_24` (`d ≥ 24`, `5 * d - 4` central blocking markers),
  `convex_partition_counterexample_ge_36` (`d ≥ 36`, `5 * d` central blocking markers without `[AKS]`),
  and `convex_partition_counterexample_ge_18` (`d ≥ 18`, conditional on `Δ⁸⁹ → ℝ¹⁶` and
  `5 * d` central blocking markers).
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

/-- `p` blocks central six-partitions if every six-partition of `unitBall d`
(possibly with degenerate parts) whose parts all contain the origin `0` has some
marker `p a` in the interior of some part. -/
def IsBlocking {d m : ℕ} (p : Fin m → Ambient d) : Prop :=
  ∀ C : Fin 6 → Body d,
    unitBall d = (⋃ i, (C i : Set (Ambient d))) →
    (∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d)))) →
    (∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) →
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

/-- **General `(k + 1)`-fold binary join of Theorem A**: for every `k : ℕ`, there is an
unconditional almost six-embedding `Δ^(36 * (k + 1) - 1) → ℝ^(7 * (k + 1) - 1)`. -/
theorem kfold_tverberg_join (k : ℕ) :
    ∃ f : (Fin (36 * (k + 1)) → ℝ) → (Fin (7 * (k + 1) - 1) → ℝ),
      IsAlmostSixEmbedding f := by
  induction k with
  | zero => exact tverberg_counterexample
  | succ k ih =>
    obtain ⟨f₁, hf₁⟩ := ih
    obtain ⟨f₀, hf₀⟩ := tverberg_counterexample
    obtain ⟨f, hf⟩ := join_almostSixEmbedding hf₁ hf₀
    exact reindex_almostSixEmbedding (by omega : 36 * (k + 1) + 36 = 36 * (k + 1 + 1))
      (by omega : (7 * (k + 1) - 1) + 6 + 1 = 7 * (k + 1 + 1) - 1) hf

/-- **Padded `41`-fold join (`d ≥ 288`, no `[AKS]`)**: for every `d ≥ 288`, there exists an
unconditional almost six-embedding `Δ^(5d+35) → ℝ^(d-2)` (`5d + 36` vertices). -/
theorem padded_tverberg_ge_288 (d : ℕ) (hd : 288 ≤ d) :
    ∃ g : (Fin (5 * d + 36) → ℝ) → (Fin (d - 2) → ℝ),
      IsAlmostSixEmbedding g := by
  obtain ⟨g₀, hg₀⟩ := kfold_tverberg_join 40
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 288) hg₀
  exact reindex_almostSixEmbedding (by omega : 36 * (40 + 1) + 5 * (d - 288) = 5 * d + 36)
    (by omega : (7 * (40 + 1) - 1) + (d - 288) = d - 2) hg

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

/-! ### Helper 2.5: Blaschke selection theorem and central-avoidance margin (Lemma 5.2) -/

private def bodyToNC {d : ℕ} (C : Body d) : TopologicalSpace.NonemptyCompacts (Ambient d) :=
  ⟨⟨(C : Set (Ambient d)), C.isCompact⟩, C.nonempty⟩

private lemma isometry_bodyToNC {d : ℕ} : Isometry (bodyToNC (d := d)) :=
  Isometry.of_dist_eq fun C D => by
    change Metric.hausdorffDist (C : Set (Ambient d)) D = dist C D
    exact ConvexBody.hausdorffDist_coe C D

private lemma continuous_infDist_body {d : ℕ} (x : Ambient d) :
    Continuous (fun C : Body d => Metric.infDist x (C : Set (Ambient d))) :=
  (LipschitzWith.of_le_add fun C D => by
    have h := Metric.infDist_le_infDist_add_hausdorffDist (x := x)
      (s := (D : Set (Ambient d))) (t := (C : Set (Ambient d))) ConvexBody.hausdorffEDist_ne_top
    rw [ConvexBody.hausdorffDist_coe, dist_comm D C] at h
    exact h).continuous

private lemma convex_iff_infDist_ineq {d : ℕ}
    (K : TopologicalSpace.NonemptyCompacts (Ambient d)) :
    Convex ℝ (K : Set (Ambient d)) ↔
      ∀ (x y : Ambient d) (a b : ℝ),
        0 ≤ a → 0 ≤ b → a + b = 1 →
        Metric.infDist (a • x + b • y) (K : Set (Ambient d)) ≤
          a * Metric.infDist x (K : Set (Ambient d)) +
          b * Metric.infDist y (K : Set (Ambient d)) := by
  constructor
  · intro hK x y a b ha hb hab
    obtain ⟨u, hu, hux⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    obtain ⟨v, hv, hvy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty y
    have hmem : a • u + b • v ∈ (K : Set (Ambient d)) :=
      convex_iff_add_mem.mp hK hu hv ha hb hab
    have hdiff : (a • x + b • y) - (a • u + b • v) = a • (x - u) + b • (y - v) := by
      simp only [smul_sub]
      abel
    calc
      Metric.infDist (a • x + b • y) (K : Set (Ambient d))
        ≤ dist (a • x + b • y) (a • u + b • v) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖a • (x - u) + b • (y - v)‖ := by rw [dist_eq_norm, hdiff]
      _ ≤ ‖a • (x - u)‖ + ‖b • (y - v)‖ := norm_add_le _ _
      _ = a * ‖x - u‖ + b * ‖y - v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ = a * Metric.infDist x (K : Set (Ambient d)) + b * Metric.infDist y (K : Set (Ambient d)) := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← hux, ← hvy]
  · intro hineq
    refine convex_iff_add_mem.mpr fun x hx y hy a b ha hb hab => ?_
    have hx0 : Metric.infDist x (K : Set (Ambient d)) = 0 := Metric.infDist_zero_of_mem hx
    have hy0 : Metric.infDist y (K : Set (Ambient d)) = 0 := Metric.infDist_zero_of_mem hy
    have hle : Metric.infDist (a • x + b • y) (K : Set (Ambient d)) ≤ 0 := by
      have h := hineq x y a b ha hb hab
      rw [hx0, hy0, mul_zero, mul_zero, add_zero] at h
      exact h
    have hzero : Metric.infDist (a • x + b • y) (K : Set (Ambient d)) = 0 :=
      le_antisymm hle Metric.infDist_nonneg
    exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).2 hzero

private lemma isClosed_range_bodyToNC {d : ℕ} :
    IsClosed (Set.range (bodyToNC (d := d))) := by
  let S : Set (TopologicalSpace.NonemptyCompacts (Ambient d)) :=
    ⋂ (x : Ambient d) (y : Ambient d)
      (c : {p : ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1}),
      {K | Metric.infDist (c.1.1 • x + c.1.2 • y) (K : Set (Ambient d)) ≤
        c.1.1 * Metric.infDist x (K : Set (Ambient d)) +
        c.1.2 * Metric.infDist y (K : Set (Ambient d))}
  have hS_closed : IsClosed S := by
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun c => ?_
    refine isClosed_le
      (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const (c.1.1 • x + c.1.2 • y)).continuous
      (((continuous_const.mul
          (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const x).continuous)).add
        (continuous_const.mul
          (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const y).continuous))
  have h_eq : Set.range (bodyToNC (d := d)) = S := by
    ext K
    constructor
    · rintro ⟨C, rfl⟩
      simp only [S, Set.mem_iInter, Set.mem_ofPred_eq]
      intro x y c
      exact (convex_iff_infDist_ineq (bodyToNC C)).mp C.convex x y c.1.1 c.1.2 c.2.1 c.2.2.1 c.2.2.2
    · intro hK
      have hconv : Convex ℝ (K : Set (Ambient d)) := by
        refine (convex_iff_infDist_ineq K).mpr fun x y a b ha hb hab => ?_
        simp only [S, Set.mem_iInter, Set.mem_ofPred_eq] at hK
        exact hK x y ⟨(a, b), ha, hb, hab⟩
      refine ⟨⟨(K : Set (Ambient d)), hconv, K.isCompact, K.nonempty⟩, ?_⟩
      ext
      rfl
  rw [h_eq]
  exact hS_closed

private lemma isClosedEmbedding_bodyToNC {d : ℕ} :
    Topology.IsClosedEmbedding (bodyToNC (d := d)) where
  __ := isometry_bodyToNC.isEmbedding
  isClosed_range := isClosed_range_bodyToNC

/-- **Blaschke Selection Theorem**: compact convex bodies contained in the closed unit ball
form a compact subset of `ConvexBody (Ambient d)` with the Hausdorff metric. -/
theorem blaschke_isCompact_subsets_unitBall (d : ℕ) :
    IsCompact {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d} := by
  have hK :
      IsCompact {K : TopologicalSpace.NonemptyCompacts (Ambient d) | (K : Set (Ambient d)) ⊆ unitBall d} :=
    TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
      (isCompact_closedBall (0 : Ambient d) 1)
  have hpre :
      {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d} =
        bodyToNC ⁻¹' {K : TopologicalSpace.NonemptyCompacts (Ambient d) | (K : Set (Ambient d)) ⊆ unitBall d} := by
    ext C
    rfl
  rw [hpre]
  exact isClosedEmbedding_bodyToNC.isCompact_preimage hK

/-- **Central-avoidance margin (Lemma 5.2)**: if `p` blocks all central six-partitions of
`unitBall d`, there exists `eta ∈ (0, 1)` such that every six-partition whose parts all meet
`eta • unitBall d` contains some marker `p a` in the interior of some part. -/
theorem exists_eta_of_isBlocking {d m : ℕ} (hd : 0 < d)
    {p : Fin m → Ambient d} (hp : IsBlocking p) :
    ∃ eta : ℝ,
      0 < eta ∧ eta < 1 ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, ∃ x ∈ (C i : Set (Ambient d)), ‖x‖ ≤ eta) →
        ∃ i a, p a ∈ interior (C i : Set (Ambient d)) := by
  let Q : Set (Fin 6 → Body d) :=
    Set.pi Set.univ fun _ : Fin 6 => {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d}
  have hQ_compact : IsCompact Q :=
    isCompact_univ_pi fun _ => blaschke_isCompact_subsets_unitBall d
  let Cov : Set (Fin 6 → Body d) :=
    ⋂ x ∈ unitBall d,
      {C : Fin 6 → Body d | (∏ i : Fin 6, Metric.infDist x (C i : Set (Ambient d))) = 0}
  let Disj : Set (Fin 6 → Body d) :=
    ⋂ (i : Fin 6) (j : Fin 6) (_ : i ≠ j) (x : Ambient d),
      {C : Fin 6 → Body d | inwardDist x (C i) * inwardDist x (C j) = 0}
  let NoMark : Set (Fin 6 → Body d) :=
    ⋂ (i : Fin 6) (a : Fin m),
      {C : Fin 6 → Body d | inwardDist (p a) (C i) = 0}
  have hCov_closed : IsClosed Cov := by
    refine isClosed_biInter fun x _ => isClosed_eq ?_ continuous_const
    exact continuous_finsetProd Finset.univ fun i _ =>
      (continuous_infDist_body x).comp (continuous_apply i)
  have hDisj_closed : IsClosed Disj := by
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun x => isClosed_eq ?_ continuous_const
    exact ((continuous_inwardDist hd x).comp (continuous_apply i)).mul
      ((continuous_inwardDist hd x).comp (continuous_apply j))
  have hNoMark_closed : IsClosed NoMark := by
    refine isClosed_iInter fun i => isClosed_iInter fun a => isClosed_eq ?_ continuous_const
    exact (continuous_inwardDist hd (p a)).comp (continuous_apply i)
  let S_bad : Set (Fin 6 → Body d) := Q ∩ (Cov ∩ Disj ∩ NoMark)
  have hS_compact : IsCompact S_bad :=
    hQ_compact.inter_right ((hCov_closed.inter hDisj_closed).inter hNoMark_closed)
  have hCov_iff : ∀ C : Fin 6 → Body d,
      C ∈ Cov ↔ unitBall d ⊆ (⋃ i, (C i : Set (Ambient d))) := fun C => by
    simp only [Cov, Set.mem_iInter, Set.mem_ofPred_eq, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and]
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · obtain ⟨i, hi⟩ := h x hx
      exact Set.mem_iUnion.mpr ⟨i, ((C i).isClosed.mem_iff_infDist_zero (C i).nonempty).2 hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hx)
      exact ⟨i, Metric.infDist_zero_of_mem hi⟩
  have hDisj_iff : ∀ C : Fin 6 → Body d,
      C ∈ Disj ↔
        ∀ i j, i ≠ j →
          Disjoint (interior (C i : Set (Ambient d)))
                   (interior (C j : Set (Ambient d))) := fun C => by
    simp only [Disj, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h i j hij => Set.disjoint_left.mpr fun x hxi hxj => ?_, fun h i j hij x => ?_⟩
    · have hi_pos : 0 < inwardDist x (C i) := (inwardDist_pos_iff hd x (C i)).mpr hxi
      have hj_pos : 0 < inwardDist x (C j) := (inwardDist_pos_iff hd x (C j)).mpr hxj
      have h0 : inwardDist x (C i) * inwardDist x (C j) = 0 := h i j hij x
      linarith [mul_pos hi_pos hj_pos]
    · by_cases hxi : x ∈ interior (C i : Set (Ambient d))
      · have hxj : x ∉ interior (C j : Set (Ambient d)) := Set.disjoint_left.mp (h i j hij) hxi
        have hwj : inwardDist x (C j) = 0 := by
          have hnot := (inwardDist_pos_iff hd x (C j)).not.mpr hxj
          exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
        simp [hwj]
      · have hwi : inwardDist x (C i) = 0 := by
          have hnot := (inwardDist_pos_iff hd x (C i)).not.mpr hxi
          exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
        simp [hwi]
  have hNoMark_iff : ∀ C : Fin 6 → Body d,
      C ∈ NoMark ↔ ∀ i a, p a ∉ interior (C i : Set (Ambient d)) := fun C => by
    simp only [NoMark, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h i a ha => ?_, fun h i a => ?_⟩
    · have hpos : 0 < inwardDist (p a) (C i) := (inwardDist_pos_iff hd (p a) (C i)).mpr ha
      linarith [h i a]
    · have hnot := (inwardDist_pos_iff hd (p a) (C i)).not.mpr (h i a)
      exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
  let F : (Fin 6 → Body d) → ℝ := fun C =>
    ∑ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d))
  have hF_cont : Continuous F :=
    continuous_finsetSum Finset.univ fun i _ =>
      (continuous_infDist_body (0 : Ambient d)).comp (continuous_apply i)
  have h_not_mem_Sbad : ∀ C : Fin 6 → Body d, IsSixPartition C →
      (∃ i a, p a ∈ interior (C i : Set (Ambient d))) ∨ C ∈ S_bad := by
    intro C hC
    by_cases hm : ∃ i a, p a ∈ interior (C i : Set (Ambient d))
    · exact Or.inl hm
    · right
      push Not at hm
      refine ⟨fun i _ => ?_, ⟨(hCov_iff C).mpr (by rw [hC.1]), (hDisj_iff C).mpr hC.2.2⟩,
        (hNoMark_iff C).mpr hm⟩
      rw [hC.1]
      exact Set.subset_iUnion (fun j => (C j : Set (Ambient d))) i
  by_cases hS_ne : S_bad.Nonempty
  · obtain ⟨C₀, hC₀_mem, hC₀_min⟩ := hS_compact.exists_isMinOn hS_ne hF_cont.continuousOn
    have hF_pos : 0 < F C₀ := by
      by_contra hle
      have hnonpos : F C₀ ≤ 0 := not_lt.mp hle
      have hzero : F C₀ = 0 :=
        le_antisymm hnonpos (Finset.sum_nonneg fun i _ => Metric.infDist_nonneg)
      have hzero_mem : ∀ i : Fin 6, (0 : Ambient d) ∈ (C₀ i : Set (Ambient d)) := fun i => by
        have hi0 : Metric.infDist (0 : Ambient d) (C₀ i : Set (Ambient d)) = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Metric.infDist_nonneg) |>.mp hzero i
            (Finset.mem_univ i)
        exact ((C₀ i).isClosed.mem_iff_infDist_zero (C₀ i).nonempty).2 hi0
      rcases hC₀_mem with ⟨hQ₀, ⟨hCov₀, hDisj₀⟩, hNoMark₀⟩
      have h_eq : unitBall d = (⋃ i, (C₀ i : Set (Ambient d))) :=
        subset_antisymm ((hCov_iff C₀).mp hCov₀) (Set.iUnion_subset fun i => hQ₀ i (Set.mem_univ i))
      obtain ⟨i, a, ha⟩ := hp C₀ h_eq ((hDisj_iff C₀).mp hDisj₀) hzero_mem
      exact (hNoMark_iff C₀).mp hNoMark₀ i a ha
    let eta : ℝ := min (1 / 2) (F C₀ / 12)
    have heta0 : 0 < eta := lt_min (by norm_num) (by linarith)
    have heta1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨eta, heta0, heta1, fun C hC hmeet => ?_⟩
    rcases h_not_mem_Sbad C hC with hm | hC_bad
    · exact hm
    · exfalso
      have hmin : F C₀ ≤ F C := hC₀_min hC_bad
      have hFC_le : F C ≤ 6 * eta := by
        have hterm : ∀ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) ≤ eta := by
          intro i
          obtain ⟨x, hxC, hxnorm⟩ := hmeet i
          calc
            Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) ≤ dist (0 : Ambient d) x :=
              Metric.infDist_le_dist_of_mem hxC
            _ = ‖x‖ := by rw [dist_zero_left]
            _ ≤ eta := hxnorm
        calc
          F C = ∑ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) := rfl
          _ ≤ ∑ _i : Fin 6, eta := Finset.sum_le_sum fun i _ => hterm i
          _ = 6 * eta := by simp [nsmul_eq_mul]
      have heta_bound : eta ≤ F C₀ / 12 := min_le_right _ _
      linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, fun C hC _ => ?_⟩
    rcases h_not_mem_Sbad C hC with hm | hC_bad
    · exact hm
    · exact False.elim (hS_ne ⟨C, hC_bad⟩)

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
`g : Δ^(m-1) → ℝ^(d-2)` and `m` central blocking markers `p` (`IsBlocking p`) in dimension `d ≥ 2`,
uses `exists_eta_of_isBlocking` (Lemma 5.2 / Blaschke compactness) to obtain `eta ∈ (0, 1)`,
constructs `d - 1` continuous functionals `Phi` and an absolutely continuous probability
measure `mu` (working uniformly for every `eta`-concentrated absolutely continuous measure)
such that no fair convex six-partition equalizes `Phi`. -/
theorem convex_partition_of_embedding_and_blocking {d m : ℕ} (hd : 2 ≤ d)
    {g : (Fin m → ℝ) → (Fin (d - 2) → ℝ)} (hg : IsAlmostSixEmbedding g)
    {p : Fin m → Ambient d} (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  have hd_pos : 0 < d := by omega
  obtain ⟨eta, heta0, heta1, heta_block⟩ := exists_eta_of_isBlocking hd_pos hp
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
      obtain ⟨i, a, ha⟩ := heta_block C hC fun i => by
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
    exact hPhi_obstruct C hC (fair_meets_eta_ball heta1 hpos htop hconc hC hfair)
  obtain ⟨hprob, hac, hpos, htop, hconc⟩ :=
    normalized_ball_measure_props (d := d) heta0 heta1
  exact ⟨Phi, _, hPhi_cont, hprob, hac,
    fun C hC hfair => h_unif _ hac hpos htop hconc C hC hfair⟩

/-! ### Helper 4: Central separating normals, Lemma 4.2, RREF, and generic blocking points -/

private def nonEmptyIntParts {d : ℕ} (C : Fin 6 → Body d) : Finset (Fin 6) := by
  classical exact Finset.univ.filter fun i => (interior (C i : Set (Ambient d))).Nonempty

private lemma mem_nonEmptyIntParts {d : ℕ} (C : Fin 6 → Body d) {i : Fin 6} :
    i ∈ nonEmptyIntParts C ↔ (interior (C i : Set (Ambient d))).Nonempty := by
  classical
  simp [nonEmptyIntParts]

private lemma open_subset_biUnion_closed_empty_interior {E : Type*} [TopologicalSpace E]
    {ι : Type*} [DecidableEq ι] (T : Finset ι) {f : ι → Set E}
    (hclosed : ∀ i ∈ T, IsClosed (f i))
    (hempty : ∀ i ∈ T, interior (f i) = ∅)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ ⋃ i ∈ T, f i) : U = ∅ := by
  induction T using Finset.induction_on generalizing U with
  | empty =>
    simpa only [Finset.notMem_empty, Set.iUnion_false, Set.iUnion_empty, Set.subset_empty_iff]
      using hsub
  | @insert i₀ T' _ ih =>
    have hclosed_T' : ∀ i ∈ T', IsClosed (f i) :=
      fun i hi => hclosed i (Finset.mem_insert_of_mem hi)
    have hempty_T' : ∀ i ∈ T', interior (f i) = ∅ :=
      fun i hi => hempty i (Finset.mem_insert_of_mem hi)
    have hU_sdiff : IsOpen (U \ f i₀) :=
      hU.sdiff (hclosed i₀ (Finset.mem_insert_self i₀ T'))
    have hsub_sdiff : U \ f i₀ ⊆ ⋃ i ∈ T', f i := by
      rintro x ⟨hxU, hxnot⟩
      have hx' := hsub hxU
      simp only [Set.mem_iUnion, Finset.mem_insert] at hx' ⊢
      rcases hx' with ⟨i, rfl | hi', hxi⟩
      · exact False.elim (hxnot hxi)
      · exact ⟨i, hi', hxi⟩
    have hdiff_empty : U \ f i₀ = ∅ := ih hclosed_T' hempty_T' hU_sdiff hsub_sdiff
    have hU_sub : U ⊆ f i₀ := Set.sdiff_eq_empty.mp hdiff_empty
    have hU_sub_int : U ⊆ interior (f i₀) := interior_maximal hU_sub hU
    rw [hempty i₀ (Finset.mem_insert_self i₀ T'), Set.subset_empty_iff] at hU_sub_int
    exact hU_sub_int

private lemma unitBall_subset_biUnion_nonempty_interior {d : ℕ}
    (C : Fin 6 → Body d) (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d)))) :
    unitBall d ⊆ ⋃ i ∈ nonEmptyIntParts C, (C i : Set (Ambient d)) := by
  classical
  let S := nonEmptyIntParts C
  let U : Set (Ambient d) :=
    Metric.ball (0 : Ambient d) 1 \ ⋃ i ∈ S, (C i : Set (Ambient d))
  have hS_closed : IsClosed (⋃ i ∈ S, (C i : Set (Ambient d))) :=
    isClosed_biUnion_finset fun i _ => (C i).isClosed
  have hU_open : IsOpen U := Metric.isOpen_ball.sdiff hS_closed
  let T : Finset (Fin 6) := Finset.univ \ S
  have hU_sub : U ⊆ ⋃ i ∈ T, (C i : Set (Ambient d)) := by
    rintro x ⟨hx_ball, hx_notS⟩
    have hx_unit : x ∈ unitBall d := Metric.ball_subset_closedBall hx_ball
    rw [hcov, Set.mem_iUnion] at hx_unit
    obtain ⟨i, hxi⟩ := hx_unit
    have hi_notS : i ∉ S := fun hiS =>
      hx_notS (Set.mem_iUnion₂.mpr ⟨i, hiS, hxi⟩)
    have hiT : i ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi_notS⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hiT, hxi⟩
  have hU_empty : U = ∅ :=
    open_subset_biUnion_closed_empty_interior T
      (fun i _ => (C i).isClosed)
      (fun i hi => by
        have hi_notS : i ∉ S := (Finset.mem_sdiff.mp hi).2
        rw [mem_nonEmptyIntParts] at hi_notS
        exact Set.not_nonempty_iff_eq_empty.mp hi_notS)
      hU_open hU_sub
  have hball_sub : Metric.ball (0 : Ambient d) 1 ⊆ ⋃ i ∈ S, (C i : Set (Ambient d)) :=
    Set.sdiff_eq_empty.mp hU_empty
  have hcl := closure_mono hball_sub
  rw [closure_ball (0 : Ambient d) one_ne_zero, hS_closed.closure_eq] at hcl
  exact hcl

private lemma exists_central_separating_normals {d : ℕ}
    (C : Fin 6 → Body d)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d))))
    (h0 : ∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) :
    ∃ n : Fin 6 → Fin 6 → Ambient d,
      (∀ i, n i i = 0) ∧
      (∀ i j, n j i = - n i j) ∧
      (∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
        n i j ≠ 0 ∧
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
        (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0) ∧
        (∀ x ∈ interior (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ < 0)) := by
  let S := nonEmptyIntParts C
  have h_pair_lt : ∀ i j : Fin 6, i ∈ S → j ∈ S → i < j →
      ∃ v : Ambient d, v ≠ 0 ∧
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪v, y⟫_ℝ) ∧
        (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪v, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪v, x⟫_ℝ ≤ 0) ∧
        (∀ x ∈ interior (C j : Set (Ambient d)), ⟪v, x⟫_ℝ < 0) := by
    intro i j hiS hjS hij
    have hi_ne : (interior (C i : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hiS
    have hj_ne : (interior (C j : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hjS
    obtain ⟨f, u, hf_lt, hf_gt⟩ := geometric_hahn_banach_open_open
      (C j).convex.interior isOpen_interior (C i).convex.interior isOpen_interior
      (hdisj j i hij.ne')
    let v : Ambient d := (InnerProductSpace.toDual ℝ (Ambient d)).symm f
    have hv_eq : ∀ z, ⟪v, z⟫_ℝ = f z := fun z => InnerProductSpace.toDual_symm_apply
    have hCi_cl : closure (interior (C i : Set (Ambient d))) = (C i : Set (Ambient d)) :=
      ((C i).convex.closure_interior_eq_closure_of_nonempty_interior hi_ne).trans
        (C i).isClosed.closure_eq
    have hCj_cl : closure (interior (C j : Set (Ambient d))) = (C j : Set (Ambient d)) :=
      ((C j).convex.closure_interior_eq_closure_of_nonempty_interior hj_ne).trans
        (C j).isClosed.closure_eq
    have h_le_Ci : ∀ y ∈ (C i : Set (Ambient d)), u ≤ f y := by
      have hsub : interior (C i : Set (Ambient d)) ⊆ {y | u ≤ f y} :=
        fun y hy => (hf_gt y hy).le
      have hclosed : IsClosed {y : Ambient d | u ≤ f y} :=
        isClosed_le continuous_const f.continuous
      intro y hy
      rw [← hCi_cl] at hy
      exact hclosed.closure_subset_iff.mpr hsub hy
    have h_le_Cj : ∀ x ∈ (C j : Set (Ambient d)), f x ≤ u := by
      have hsub : interior (C j : Set (Ambient d)) ⊆ {x | f x ≤ u} :=
        fun x hx => (hf_lt x hx).le
      have hclosed : IsClosed {x : Ambient d | f x ≤ u} :=
        isClosed_le f.continuous continuous_const
      intro x hx
      rw [← hCj_cl] at hx
      exact hclosed.closure_subset_iff.mpr hsub hx
    have hu0 : u = 0 := by
      have h0i := h_le_Ci 0 (h0 i)
      have h0j := h_le_Cj 0 (h0 j)
      rw [map_zero] at h0i h0j
      linarith
    subst hu0
    obtain ⟨y₀, hy₀⟩ := hi_ne
    have hv_ne : v ≠ 0 := by
      intro hv0
      have := hf_gt y₀ hy₀
      rw [← hv_eq, hv0, inner_zero_left] at this
      exact lt_irrefl 0 this
    refine ⟨v, hv_ne, ?_, ?_, ?_, ?_⟩
    · intro y hy; rw [hv_eq]; exact h_le_Ci y hy
    · intro y hy; rw [hv_eq]; exact hf_gt y hy
    · intro x hx; rw [hv_eq]; exact h_le_Cj x hx
    · intro x hx; rw [hv_eq]; exact hf_lt x hx
  classical
  let n_lt : Fin 6 → Fin 6 → Ambient d := fun i j =>
    if h : i ∈ S ∧ j ∈ S ∧ i < j then
      Classical.choose (h_pair_lt i j h.1 h.2.1 h.2.2)
    else 0
  let n : Fin 6 → Fin 6 → Ambient d := fun i j =>
    if i < j then n_lt i j else if j < i then - n_lt j i else 0
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [n]
  · intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hnot : ¬ (j < i) := hij.not_gt
      simp [n, hij, hnot]
    · simp [n]
    · have hnot : ¬ (i < j) := hij.not_gt
      simp [n, hij, hnot]
  · intro i j hij
    have hn_lt : ∀ a b, a ∉ S ∨ b ∉ S → n_lt a b = 0 := fun a b hab => by
      dsimp [n_lt]
      split_ifs with h
      · exact absurd h.1 (hab.elim id fun hb' => absurd h.2.1 hb')
      · rfl
    rcases lt_trichotomy i j with hij' | rfl | hij'
    · simp [n, hij', hn_lt i j hij]
    · simp [n]
    · have hji : ¬ (i < j) := hij'.not_gt
      simp [n, hij', hji, hn_lt j i hij.symm]
  · intro i hiS j hjS hij_ne
    rcases lt_or_gt_of_ne hij_ne with hij | hij
    · have hspec := Classical.choose_spec (h_pair_lt i j hiS hjS hij)
      have hn_eq : n i j = n_lt i j := by simp [n, hij]
      have hn_lt_eq : n_lt i j = Classical.choose (h_pair_lt i j hiS hjS hij) := by
        dsimp [n_lt]
        split_ifs with h'
        · rfl
        · exact False.elim (h' ⟨hiS, hjS, hij⟩)
      simpa [hn_eq, hn_lt_eq] using hspec
    · have hspec := Classical.choose_spec (h_pair_lt j i hjS hiS hij)
      have hn_eq : n i j = - n_lt j i := by simp [n, hij, hij.not_gt]
      have hn_lt_eq : n_lt j i = Classical.choose (h_pair_lt j i hjS hiS hij) := by
        dsimp [n_lt]
        split_ifs with h'
        · rfl
        · exact False.elim (h' ⟨hjS, hiS, hij⟩)
      rw [hn_eq, hn_lt_eq]
      rcases hspec with ⟨hv_ne, hCj, hCj_int, hCi, hCi_int⟩
      refine ⟨neg_ne_zero.mpr hv_ne, ?_, ?_, ?_, ?_⟩
      · intro y hy; rw [inner_neg_left]; linarith [hCi y hy]
      · intro y hy; rw [inner_neg_left]; linarith [hCi_int y hy]
      · intro x hx; rw [inner_neg_left]; linarith [hCj x hx]
      · intro x hx; rw [inner_neg_left]; linarith [hCj_int x hx]

private lemma skeleton_in_separating_hyperplanes {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hsym : ∀ i j, n j i = - n i j)
    {x : Ambient d} (hx_ball : x ∈ Metric.ball (0 : Ambient d) 1)
    (hx_not_int : ∀ i : Fin 6, x ∉ interior (C i : Set (Ambient d))) :
    ∃ i ∈ nonEmptyIntParts C, ∃ j ∈ nonEmptyIntParts C, i < j ∧ ⟪n i j, x⟫_ℝ = 0 := by
  classical
  let S := nonEmptyIntParts C
  have hS_cov := unitBall_subset_biUnion_nonempty_interior C hcov
  have hx_S : x ∈ ⋃ i ∈ S, (C i : Set (Ambient d)) :=
    hS_cov (Metric.ball_subset_closedBall hx_ball)
  rw [Set.mem_iUnion₂] at hx_S
  obtain ⟨i, hiS, hxi⟩ := hx_S
  have hex_j : ∃ j ∈ S, j ≠ i ∧ ⟪n i j, x⟫_ℝ = 0 := by
    by_contra h_none
    push Not at h_none
    have hpos_j : ∀ j ∈ S.erase i, 0 < ⟪n i j, x⟫_ℝ := by
      intro j hj
      have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hle : 0 ≤ ⟪n i j, x⟫_ℝ := (hsep i hiS j hjS hji.symm).1 x hxi
      exact lt_of_le_of_ne hle (Ne.symm (h_none j hjS hji))
    let U : Set (Ambient d) :=
      Metric.ball (0 : Ambient d) 1 ∩ ⋂ j ∈ S.erase i, {y : Ambient d | 0 < ⟪n i j, y⟫_ℝ}
    have hU_open : IsOpen U :=
      Metric.isOpen_ball.inter <| isOpen_biInter_finset fun j _ =>
        isOpen_lt continuous_const (continuous_const.inner continuous_id)
    have hxU : x ∈ U := ⟨hx_ball, Set.mem_iInter₂.mpr hpos_j⟩
    have hU_sub : U ⊆ (C i : Set (Ambient d)) := by
      intro y hyU
      have hy_S : y ∈ ⋃ k ∈ S, (C k : Set (Ambient d)) :=
        hS_cov (Metric.ball_subset_closedBall hyU.1)
      rw [Set.mem_iUnion₂] at hy_S
      obtain ⟨k, hkS, hyk⟩ := hy_S
      by_cases hki : k = i
      · exact hki ▸ hyk
      · have hk_er : k ∈ S.erase i := Finset.mem_erase.mpr ⟨hki, hkS⟩
        have hpos : 0 < ⟪n i k, y⟫_ℝ := Set.mem_iInter₂.mp hyU.2 k hk_er
        have hle : ⟪n i k, y⟫_ℝ ≤ 0 := (hsep i hiS k hkS (Ne.symm hki)).2 y hyk
        exact False.elim (not_lt_of_ge hle hpos)
    exact hx_not_int i (interior_maximal hU_sub hU_open hxU)
  obtain ⟨j, hjS, hji, hzero⟩ := hex_j
  rcases lt_or_gt_of_ne hji with hij | hij
  · refine ⟨j, hjS, i, hiS, hij, ?_⟩
    rw [hsym, inner_neg_left, hzero, neg_zero]
  · exact ⟨i, hiS, j, hjS, hij, hzero⟩

/-- **Lemma 4.2 (Normal rank ≤ 5)**: for separating normals `n` of a central six-partition,
the vectors `a i = ∑ j, n i j` annihilate the same vectors as all `n i j`. -/
private lemma central_partition_normal_rank {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hsym : ∀ i j, n j i = - n i j)
    {v : Ambient d}
    (hv : ∀ i : Fin 6, ⟪∑ j : Fin 6, n i j, v⟫_ℝ = 0) :
    ∀ i j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
  classical
  let S := nonEmptyIntParts C
  have hS_cov := unitBall_subset_biUnion_nonempty_interior C hcov
  let Sv : Finset (Fin 6) := S.filter fun i => ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ
  have hSv_zero : ∀ i ∈ Sv, ∀ j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
    intro i hiSv
    have hiS : i ∈ S := (Finset.mem_filter.mp hiSv).1
    have hnonneg_S : ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ := (Finset.mem_filter.mp hiSv).2
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 6)), 0 ≤ ⟪n i j, v⟫_ℝ := by
      intro j _
      by_cases hjS : j ∈ S
      · exact hnonneg_S j hjS
      · simp [hnotS i j (Or.inr hjS)]
    have hsum0 : ∑ j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
      simpa only [sum_inner] using hv i
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 j (Finset.mem_univ j)
  have hzero_diag : ∀ i : Fin 6, n i i = 0 := fun i => by
    have hadd : n i i + n i i = 0 := by
      conv_lhs => rhs; rw [hsym i i]
      exact add_neg_cancel _
    have h2 : (2 : ℝ) • n i i = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hSv_ne : Sv.Nonempty := by
    let α : ℝ := (‖v‖ + 1)⁻¹
    have hα_pos : 0 < α := inv_pos.mpr (by positivity)
    let w : Ambient d := α • v
    have hw_ball : w ∈ unitBall d := by
      change dist (α • v) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hα_pos.le]
      dsimp [α]
      rw [inv_mul_le_one₀ (by positivity)]
      linarith
    have hw_S : w ∈ ⋃ i ∈ S, (C i : Set (Ambient d)) := hS_cov hw_ball
    rw [Set.mem_iUnion₂] at hw_S
    obtain ⟨i, hiS, hwi⟩ := hw_S
    refine ⟨i, Finset.mem_filter.mpr ⟨hiS, fun j hjS => ?_⟩⟩
    by_cases hij : i = j
    · subst hij
      rw [hzero_diag i, inner_zero_left]
    · have hnonneg_w : 0 ≤ ⟪n i j, w⟫_ℝ := (hsep i hiS j hjS hij).1 w hwi
      dsimp [w] at hnonneg_w
      rw [real_inner_smul_right] at hnonneg_w
      exact nonneg_of_mul_nonneg_right hnonneg_w hα_pos
  have hS_sub_Sv : S ⊆ Sv := by
    by_contra hnot_sub
    obtain ⟨k, hkS, hk_not_Sv⟩ := Finset.not_subset.mp hnot_sub
    have hk_ne : (interior (C k : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hkS
    obtain ⟨x, hx_int⟩ := hk_ne
    have hex_neg : ∀ i ∈ S \ Sv, ∃ j ∈ S, ⟪n i j, v⟫_ℝ < 0 := by
      intro i hi
      obtain ⟨hiS, hi_not_Sv⟩ := Finset.mem_sdiff.mp hi
      have hnot : ¬ ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ := fun h =>
        hi_not_Sv (Finset.mem_filter.mpr ⟨hiS, h⟩)
      push Not at hnot
      exact hnot
    choose jOf hjOf_mem hjOf_neg using hex_neg
    let t : ℝ :=
      1 + ∑ i ∈ S \ Sv,
        if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0
    have hterm_nonneg : ∀ i ∈ S \ Sv,
        0 ≤ (if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0) := by
      intro i hi
      simp only [hi, ↓reduceDIte]
      exact div_nonneg (abs_nonneg _) (by linarith [hjOf_neg i hi])
    have ht_pos : 0 < t := by
      have hsum_nn := Finset.sum_nonneg hterm_nonneg
      dsimp [t]
      linarith
    let y : Ambient d := x + t • v
    let β : ℝ := (‖y‖ + 1)⁻¹
    have hβ_pos : 0 < β := inv_pos.mpr (by positivity)
    let z : Ambient d := β • y
    have hz_ball : z ∈ unitBall d := by
      change dist (β • y) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hβ_pos.le]
      dsimp [β]
      rw [inv_mul_le_one₀ (by positivity)]
      linarith
    have hz_S : z ∈ ⋃ m ∈ S, (C m : Set (Ambient d)) := hS_cov hz_ball
    rw [Set.mem_iUnion₂] at hz_S
    obtain ⟨m, hmS, hzm⟩ := hz_S
    have hy_nonneg : ∀ j ∈ S, m ≠ j → 0 ≤ ⟪n m j, y⟫_ℝ := by
      intro j hjS hmj
      have hzw : 0 ≤ ⟪n m j, z⟫_ℝ := (hsep m hmS j hjS hmj).1 z hzm
      dsimp [z] at hzw
      rw [real_inner_smul_right] at hzw
      exact nonneg_of_mul_nonneg_right hzw hβ_pos
    by_cases hmSv : m ∈ Sv
    · have hmk_ne : m ≠ k := fun h => hk_not_Sv (h ▸ hmSv)
      have hy_mk : 0 ≤ ⟪n m k, y⟫_ℝ := hy_nonneg k hkS hmk_ne
      have hv_mk : ⟪n m k, v⟫_ℝ = 0 := hSv_zero m hmSv k
      have hx_km : 0 < ⟪n k m, x⟫_ℝ := (hsep k hkS m hmS hmk_ne.symm).2 x hx_int
      have hx_mk : ⟪n m k, x⟫_ℝ < 0 := by
        rw [hsym k m, inner_neg_left]
        linarith
      dsimp [y] at hy_mk
      rw [inner_add_right, real_inner_smul_right, hv_mk, mul_zero, add_zero] at hy_mk
      linarith
    · have hm_sdiff : m ∈ S \ Sv := Finset.mem_sdiff.mpr ⟨hmS, hmSv⟩
      let j : Fin 6 := jOf m hm_sdiff
      have hjS : j ∈ S := hjOf_mem m hm_sdiff
      have hv_mj : ⟪n m j, v⟫_ℝ < 0 := hjOf_neg m hm_sdiff
      have hmj_ne : m ≠ j := by
        intro hmj
        have hm0 : ⟪n m m, v⟫_ℝ = 0 := by rw [hzero_diag m, inner_zero_left]
        rw [← hmj, hm0] at hv_mj
        exact lt_irrefl 0 hv_mj
      have hy_mj : 0 ≤ ⟪n m j, y⟫_ℝ := hy_nonneg j hjS hmj_ne
      have hsingle :
          |⟪n m j, x⟫_ℝ| / (-⟪n m j, v⟫_ℝ) ≤
            ∑ i ∈ S \ Sv,
              if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0 := by
        have hle := Finset.single_le_sum hterm_nonneg hm_sdiff
        simpa [hm_sdiff, j] using hle
      have hb_pos : 0 < -⟪n m j, v⟫_ℝ := by linarith
      have ht_gt : |⟪n m j, x⟫_ℝ| / (-⟪n m j, v⟫_ℝ) < t := by
        dsimp [t]
        linarith
      have hmul_gt : |⟪n m j, x⟫_ℝ| < t * (-⟪n m j, v⟫_ℝ) :=
        (div_lt_iff₀ hb_pos).mp ht_gt
      have h_le_abs : ⟪n m j, x⟫_ℝ ≤ |⟪n m j, x⟫_ℝ| := le_abs_self _
      dsimp [y] at hy_mj
      rw [inner_add_right, real_inner_smul_right] at hy_mj
      linarith
  intro i j
  by_cases hiS : i ∈ S
  · exact hSv_zero i (hS_sub_Sv hiS) j
  · simp [hnotS i j (Or.inl hiS)]

/-- Gaussian elimination to Reduced Row Echelon Form (RREF) for any tuple of `k ≤ d` vectors. -/
private lemma exists_rref {d : ℕ} (k : ℕ) (hk : k ≤ d) (A : Fin k → Ambient d) :
    ∃ (I : Fin k → Fin d) (u : Fin k → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin k, u r (I s) = if r = s then 1 else 0) ∧
      (∀ t : Fin k, A t ∈ Submodule.span ℝ (Set.range u)) := by
  induction k with
  | zero =>
    exact ⟨finZeroElim, finZeroElim, Function.injective_of_subsingleton _,
      fun r => r.elim0, fun t => t.elim0⟩
  | succ k ih =>
    let A' : Fin k → Ambient d := fun t => A t.castSucc
    obtain ⟨I', u', hI'_inj, hu'_rref, hA'_span⟩ := ih (by omega : k ≤ d) A'
    let w : Ambient d := A (Fin.last k)
    let w' : Ambient d := w - ∑ r : Fin k, (w (I' r)) • u' r
    have hw'_piv : ∀ s : Fin k, w' (I' s) = 0 := fun s => by
      have h1 : (∑ r : Fin k, (w (I' r)) • u' r) (I' s) =
          ∑ r : Fin k, w (I' r) * u' r (I' s) := by
        simp [Finset.sum_apply, smul_eq_mul]
      change w (I' s) - (∑ r : Fin k, (w (I' r)) • u' r) (I' s) = 0
      rw [h1]
      have h2 : ∑ r : Fin k, w (I' r) * u' r (I' s) = w (I' s) := by
        simp [hu'_rref]
      linarith
    have hex_step : ∃ (j₀ : Fin d) (u_new : Ambient d),
        (∀ s : Fin k, I' s ≠ j₀) ∧
        u_new j₀ = 1 ∧
        (∀ s : Fin k, u_new (I' s) = 0) ∧
        w' ∈ Submodule.span ℝ ({u_new} : Set (Ambient d)) := by
      by_cases hw'0 : w' = 0
      · have hnot_sub : ¬ Finset.univ ⊆ Finset.univ.image I' := by
          intro hsub
          have hcard := Finset.card_le_card hsub
          have hcard_img : (Finset.univ.image I').card ≤ k :=
            Finset.card_image_le.trans (by simp)
          rw [Finset.card_univ, Fintype.card_fin] at hcard
          omega
        obtain ⟨j₀, _, hj₀_not⟩ := Finset.not_subset.mp hnot_sub
        have hj₀_ne : ∀ s : Fin k, I' s ≠ j₀ := fun s h =>
          hj₀_not (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, h⟩)
        let u_new : Ambient d := EuclideanSpace.single j₀ (1 : ℝ)
        refine ⟨j₀, u_new, hj₀_ne, ?_, ?_, ?_⟩
        · simp [u_new, EuclideanSpace.single]
        · intro s
          simp [u_new, EuclideanSpace.single, (hj₀_ne s).symm]
        · rw [hw'0]
          exact Submodule.zero_mem _
      · have hex_j : ∃ j₀ : Fin d, w' j₀ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hw'0 (PiLp.ext hall)
        obtain ⟨j₀, hj₀_ne0⟩ := hex_j
        have hj₀_ne : ∀ s : Fin k, I' s ≠ j₀ := fun s h => by
          rw [← h] at hj₀_ne0
          exact hj₀_ne0 (hw'_piv s)
        let u_new : Ambient d := (w' j₀)⁻¹ • w'
        refine ⟨j₀, u_new, hj₀_ne, ?_, ?_, ?_⟩
        · change (w' j₀)⁻¹ * w' j₀ = 1
          exact inv_mul_cancel₀ hj₀_ne0
        · intro s
          change (w' j₀)⁻¹ * w' (I' s) = 0
          rw [hw'_piv s, mul_zero]
        · have hw'_eq : w' = (w' j₀) • u_new := by
            dsimp [u_new]
            rw [smul_smul, mul_inv_cancel₀ hj₀_ne0, one_smul]
          rw [hw'_eq]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u_new))
    obtain ⟨j₀, u_new, hj₀_ne, hu_new_j0, hu_new_piv, hw'_span⟩ := hex_step
    let I : Fin (k + 1) → Fin d := Fin.snoc I' j₀
    let u : Fin (k + 1) → Ambient d :=
      Fin.snoc (fun r : Fin k => u' r - (u' r j₀) • u_new) u_new
    refine ⟨I, u, ?_, ?_, ?_⟩
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · have hab' : I' a' = I' b' := by simpa [I] using hab
        exact congrArg Fin.castSucc (hI'_inj hab')
      · have hab' : I' a' = j₀ := by simpa [I] using hab
        exact False.elim (hj₀_ne a' hab')
      · have hab' : j₀ = I' b' := by simpa [I] using hab
        exact False.elim (hj₀_ne b' hab'.symm)
      · rfl
    · intro r s
      refine Fin.lastCases ?_ (fun r' => ?_) r <;>
        refine Fin.lastCases ?_ (fun s' => ?_) s
      · simp [I, u, hu_new_j0]
      · have hne : Fin.last k ≠ s'.castSucc := (Fin.castSucc_lt_last s').ne'
        change u (Fin.last k) (I s'.castSucc) = if Fin.last k = s'.castSucc then 1 else 0
        simp [hne, I, u, hu_new_piv s']
      · have hne : r'.castSucc ≠ Fin.last k := (Fin.castSucc_lt_last r').ne
        change u r'.castSucc (I (Fin.last k)) = if r'.castSucc = Fin.last k then 1 else 0
        simp [hne, I, u, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hu_new_j0]
      · simp only [Fin.castSucc_inj]
        have hstep : (u' r' - (u' r' j₀) • u_new) (I' s') = if r' = s' then 1 else 0 := by
          change (u' r' (I' s')) - (u' r' j₀) * u_new (I' s') = if r' = s' then 1 else 0
          rw [hu_new_piv s', mul_zero, sub_zero, hu'_rref r' s']
        simpa [I, u] using hstep
    · have hu_new_mem : u_new ∈ Submodule.span ℝ (Set.range u) :=
        Submodule.subset_span ⟨Fin.last k, by simp [u]⟩
      have hu'_mem : ∀ r : Fin k, u' r ∈ Submodule.span ℝ (Set.range u) := fun r => by
        have hmem : u r.castSucc ∈ Submodule.span ℝ (Set.range u) :=
          Submodule.subset_span ⟨r.castSucc, rfl⟩
        have heq : u' r = u r.castSucc + (u' r j₀) • u_new := by
          simp [u]
        rw [heq]
        exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ hu_new_mem)
      have hspan_le : Submodule.span ℝ (Set.range u') ≤ Submodule.span ℝ (Set.range u) :=
        Submodule.span_le.mpr (by rintro x ⟨r, rfl⟩; exact hu'_mem r)
      have hw'_mem : w' ∈ Submodule.span ℝ (Set.range u) := by
        have hle : Submodule.span ℝ ({u_new} : Set (Ambient d)) ≤ Submodule.span ℝ (Set.range u) :=
          Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu_new_mem)
        exact hle hw'_span
      intro t
      refine Fin.lastCases ?_ (fun t' => ?_) t
      · have hw_eq : A (Fin.last k) = w' + ∑ r : Fin k, (w (I' r)) • u' r := by
          dsimp [w', w]
          abel
        rw [hw_eq]
        refine Submodule.add_mem _ hw'_mem (Submodule.sum_mem _ fun r _ => ?_)
        exact Submodule.smul_mem _ _ (hu'_mem r)
      · exact hspan_le (hA'_span t')

/-- Pairwise separating normals of a central six-partition lie in the RREF span of
the 5 row vectors `a₁, ..., a₅`. -/
private lemma separating_normals_in_rref_span {d : ℕ} (hd : 5 ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d))))
    (h0 : ∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) :
    ∃ (n : Fin 6 → Fin 6 → Ambient d) (I : Fin 5 → Fin d) (u : Fin 5 → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin 5, u r (I s) = if r = s then 1 else 0) ∧
      (∀ i, n i i = 0) ∧
      (∀ i j, n j i = - n i j) ∧
      (∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j → n i j ≠ 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0)) ∧
      (∀ k l : Fin 6, ∀ j : Fin d,
        n k l j = ∑ r : Fin 5, n k l (I r) * u r j) := by
  obtain ⟨n, hnii, hnsym, hnnotS, hnsep⟩ := exists_central_separating_normals C hdisj h0
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := by
    have hneg : ∑ i : Fin 6, a i = - ∑ i : Fin 6, a i := by
      calc ∑ i : Fin 6, a i
          = ∑ i : Fin 6, ∑ j : Fin 6, n i j := rfl
        _ = ∑ j : Fin 6, ∑ i : Fin 6, n i j := Finset.sum_comm
        _ = ∑ j : Fin 6, ∑ i : Fin 6, (- n j i) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hnsym j i]
        _ = - ∑ j : Fin 6, ∑ i : Fin 6, n j i := by
          simp [Finset.sum_neg_distrib]
    have hadd : (∑ i : Fin 6, a i) + (∑ i : Fin 6, a i) = 0 := by
      conv_lhs => rhs; rw [hneg]
      exact add_neg_cancel _
    have h2 : (2 : ℝ) • (∑ i : Fin 6, a i) = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  let A : Fin 5 → Ambient d := fun t => a t.succ
  obtain ⟨I, u, hI_inj, hu_rref, hA_span⟩ := exists_rref 5 hd A
  have ha_span : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range u) := fun i => by
    refine Fin.cases ?_ (fun t => hA_span t) i
    have ha0 : a 0 = - ∑ t : Fin 5, A t := by
      have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
        simpa only [← Fin.sum_univ_succ] using ha_sum0
      exact eq_neg_of_add_eq_zero_left hsplit
    rw [ha0]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ => hA_span t)
  have hinner_single : ∀ (w : Ambient d) (j : Fin d),
      ⟪w, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = w j := fun w j => by
    rw [EuclideanSpace.inner_single_right, one_mul]
    simp
  have hspan_perp : ∀ {v : Ambient d},
      (∀ r : Fin 5, ⟪u r, v⟫_ℝ = 0) →
      ∀ i : Fin 6, ⟪a i, v⟫_ℝ = 0 := by
    intro v hv i
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (ha_span i)
    · rintro _ ⟨r, rfl⟩; exact hv r
    · simp
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [real_inner_smul_left, hx, mul_zero]
  have hcoef : ∀ k l : Fin 6, ∀ j : Fin d,
      n k l j = ∑ r : Fin 5, n k l (I r) * u r j := by
    intro k l j
    let v : Ambient d :=
      EuclideanSpace.single j (1 : ℝ) -
        ∑ r : Fin 5, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)
    have hv_u : ∀ s : Fin 5, ⟪u s, v⟫_ℝ = 0 := fun s => by
      dsimp [v]
      rw [inner_sub_right, inner_sum, hinner_single]
      have hsum : (∑ r : Fin 5, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) = u s j := by
        calc ∑ r : Fin 5, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ
            = ∑ r : Fin 5, u r j * u s (I r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [real_inner_smul_right, hinner_single]
          _ = ∑ r : Fin 5, u r j * (if s = r then 1 else 0) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_rref s r]
          _ = u s j := by simp
      rw [hsum, sub_self]
    have hv_n : ⟪n k l, v⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS
        (fun i hiS j hjS hij =>
          ⟨(hnsep i hiS j hjS hij).2.1, (hnsep i hiS j hjS hij).2.2.1⟩)
        hnsym (hspan_perp hv_u) k l
    dsimp [v] at hv_n
    rw [inner_sub_right, inner_sum, hinner_single] at hv_n
    have hsum_n :
        (∑ r : Fin 5, ⟪n k l, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) =
          ∑ r : Fin 5, n k l (I r) * u r j := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [real_inner_smul_right, hinner_single, mul_comm]
    linarith [hv_n, hsum_n]
  refine ⟨n, I, u, hI_inj, hu_rref, hnii, hnsym, hnnotS,
    (fun i hiS j hjS hij => (hnsep i hiS j hjS hij).1),
    (fun i hiS j hjS hij => ⟨(hnsep i hiS j hjS hij).2.1, (hnsep i hiS j hjS hij).2.2.2.1⟩),
    hcoef⟩

private abbrev Pairs (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

private abbrev Pairs6 := Pairs 6

private lemma card_pairs6 : Fintype.card Pairs6 = 15 := by decide

private abbrev RrefParamIdx {d m k : ℕ}
    (I : Fin k → Fin d) (rDom : Pairs6 → Fin k) (σ : Fin m → Pairs6) :=
  (Fin k × {j : Fin d // ∀ r, I r ≠ j}) ⊕
  ((e : Pairs6) × {r : Fin k // r ≠ rDom e}) ⊕
  ((a : Fin m) × {j : Fin d // j ≠ I (rDom (σ a))})

private structure RrefConfig (d m k : ℕ) where
  I : {I : Fin k → Fin d // Function.Injective I}
  rDom : Pairs6 → Fin k
  σ : Fin m → Pairs6

private instance (d m k : ℕ) : Finite (RrefConfig d m k) :=
  Finite.of_injective
    (fun c : RrefConfig d m k => (c.I, c.rDom, c.σ))
    (fun c₁ c₂ h => by
      cases c₁; cases c₂
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl)

private def evalPoints {d m : ℕ} (z : Fin (m * d) → ℝ) : Fin m → Ambient d :=
  fun a => (EuclideanSpace.equiv (Fin d) ℝ).symm fun j => z (finProdFinEquiv (a, j))

private lemma continuous_evalPoints {d m : ℕ} :
    Continuous (evalPoints (d := d) (m := m)) := by
  refine continuous_pi fun a => ?_
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp <|
    continuous_pi fun j => continuous_apply (finProdFinEquiv (a, j))

private def rrefParamU {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (r : Fin k) (j : Fin d) : ℝ :=
  if _h : c.I.1 r = j then 1
  else if h' : ∃ s : Fin k, c.I.1 s = j then 0
  else y (Sum.inl (r, ⟨j, fun s hs => h' ⟨s, hs⟩⟩))

private def rrefParamC {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (r : Fin k) : ℝ :=
  if h : r = c.rDom e then 1
  else y (Sum.inr (Sum.inl ⟨e, ⟨r, h⟩⟩))

private def rrefParamN {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (j : Fin d) : ℝ :=
  ∑ r : Fin k, rrefParamC c y e r * rrefParamU c y r j

private def rrefParamP0 {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.I.1 (c.rDom (c.σ a)) then 0
  else y (Sum.inr (Sum.inr ⟨a, ⟨j, h⟩⟩))

private def rrefParamMap {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) : Fin (m * d) → ℝ :=
  fun x =>
    let p := finProdFinEquiv.symm x
    if p.2 = c.I.1 (c.rDom (c.σ p.1)) then
      - ∑ j : Fin d, rrefParamN c y (c.σ p.1) j * rrefParamP0 c y p.1 j
    else
      rrefParamP0 c y p.1 p.2

private lemma differentiable_rrefParamMap {d m k : ℕ} (c : RrefConfig d m k) :
    Differentiable ℝ (rrefParamMap c) := by
  have hu : ∀ r j, Differentiable ℝ fun y => rrefParamU c y r j := fun r j => by
    dsimp [rrefParamU]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_const 0
    · exact differentiable_apply _
  have hc : ∀ e r, Differentiable ℝ fun y => rrefParamC c y e r := fun e r => by
    dsimp [rrefParamC]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_apply _
  have hn : ∀ e j, Differentiable ℝ fun y => rrefParamN c y e j := fun e j =>
    Differentiable.fun_sum fun r _ => (hc e r).mul (hu r j)
  have hp0 : ∀ a j, Differentiable ℝ fun y => rrefParamP0 c y a j := fun a j => by
    dsimp [rrefParamP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiable_pi.mpr fun x => ?_
  dsimp [rrefParamMap]
  split_ifs
  · exact (Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg
  · exact hp0 _ _

private lemma card_rrefParamIdx {d m k : ℕ}
    (c : RrefConfig d m k) :
    Fintype.card (RrefParamIdx c.I.1 c.rDom c.σ) =
      k * (d - k) + 15 * (k - 1) + m * (d - 1) := by
  have h1 : Fintype.card {j : Fin d // ∀ r : Fin k, c.I.1 r ≠ j} = d - k := by
    let sRest : Finset (Fin d) := Finset.univ \ Finset.univ.image c.I.1
    have heq : {j : Fin d // ∀ r : Fin k, c.I.1 r ≠ j} ≃ {j : Fin d // j ∈ sRest} :=
      Equiv.subtypeEquivRight fun j => by
        simp [sRest, Finset.mem_sdiff, Finset.mem_image]
    rw [Fintype.card_congr heq, Fintype.card_coe]
    have hsub : Finset.univ.image c.I.1 ⊆ (Finset.univ : Finset (Fin d)) :=
      Finset.subset_univ _
    dsimp [sRest]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ c.I.2, Finset.card_univ, Fintype.card_fin]
  have h2 : ∀ e : Pairs6, Fintype.card {r : Fin k // r ≠ c.rDom e} = k - 1 := fun e => by
    have heq : {r : Fin k // r ≠ c.rDom e} ≃
        {r : Fin k // r ∈ Finset.univ.erase (c.rDom e)} :=
      Equiv.subtypeEquivRight fun r => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have h3 : ∀ a : Fin m, Fintype.card {j : Fin d // j ≠ c.I.1 (c.rDom (c.σ a))} = d - 1 :=
    fun a => by
    have heq : {j : Fin d // j ≠ c.I.1 (c.rDom (c.σ a))} ≃
        {j : Fin d // j ∈ Finset.univ.erase (c.I.1 (c.rDom (c.σ a)))} :=
      Equiv.subtypeEquivRight fun j => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  simp only [RrefParamIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fin, h1, h2, h3, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_pairs6]
  ring

private lemma volume_image_eq_zero_of_card_lt {N : ℕ} (hN : 0 < N)
    {γ : Type*} [Fintype γ] (hcard : Fintype.card γ < N)
    {U : Set (γ → ℝ)} {Ψ : (γ → ℝ) → (Fin N → ℝ)} (hΨ : DifferentiableOn ℝ Ψ U) :
    (volume : Measure (Fin N → ℝ)) (Ψ '' U) = 0 := by
  let k0 : Fin N := ⟨0, hN⟩
  let H₀ : Submodule ℝ (Fin N → ℝ) := LinearMap.ker (LinearMap.proj k0)
  have hH₀_ne_top : H₀ ≠ ⊤ := by
    intro htop
    have hmem : Pi.single (M := fun _ : Fin N => ℝ) k0 (1 : ℝ) ∈ H₀ := htop ▸ Submodule.mem_top
    have h0 : (Pi.single (M := fun _ : Fin N => ℝ) k0 (1 : ℝ)) k0 = 0 := hmem
    simp at h0
  have hH₀_vol : (volume : Measure (Fin N → ℝ)) (H₀ : Set (Fin N → ℝ)) = 0 :=
    Measure.addHaar_submodule volume H₀ hH₀_ne_top
  let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
  let ι : γ → Fin N := fun g => ⟨(e g).1 + 1, by have := (e g).isLt; omega⟩
  let L : (Fin N → ℝ) → (γ → ℝ) := fun z g => z (ι g)
  have hL_diff : Differentiable ℝ L := differentiable_pi.mpr fun g => differentiable_apply (ι g)
  let M : (γ → ℝ) → (Fin N → ℝ) := fun y k =>
    if hk : k.1 = 0 then 0
    else if hlt : k.1 - 1 < Fintype.card γ then y (e.symm ⟨k.1 - 1, hlt⟩)
    else 0
  have hM_mem : ∀ y, M y ∈ (H₀ : Set (Fin N → ℝ)) := fun y => by
    change M y k0 = 0
    simp [M, k0]
  have hLM : ∀ y, L (M y) = y := fun y => by
    funext g
    dsimp [L, M]
    have hlt : (ι g).1 - 1 < Fintype.card γ := by simp [ι]
    simp only [↓reduceDIte, hlt]
    have heq : (⟨(ι g).1 - 1, hlt⟩ : Fin (Fintype.card γ)) = e g := by
      ext; simp [ι]
    rw [heq, e.symm_apply_apply]
  let s : Set (Fin N → ℝ) := (H₀ : Set (Fin N → ℝ)) ∩ L ⁻¹' U
  have hs_vol : (volume : Measure (Fin N → ℝ)) s = 0 :=
    measure_mono_null Set.inter_subset_left hH₀_vol
  have hsub : Ψ '' U ⊆ (Ψ ∘ L) '' s := by
    rintro _ ⟨y, hyU, rfl⟩
    refine ⟨M y, ⟨hM_mem y, ?_⟩, ?_⟩
    · simpa [Set.mem_preimage, hLM y] using hyU
    · simp [Function.comp_apply, hLM y]
  have hcomp_diff : DifferentiableOn ℝ (Ψ ∘ L) s :=
    hΨ.comp hL_diff.differentiableOn fun _ hz => hz.2
  have himg_zero : (volume : Measure (Fin N → ℝ)) ((Ψ ∘ L) '' s) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (volume : Measure (Fin N → ℝ)) hcomp_diff hs_vol
  exact measure_mono_null hsub himg_zero

private lemma volume_range_eq_zero_of_card_lt {N : ℕ} (hN : 0 < N)
    {γ : Type*} [Fintype γ] (hcard : Fintype.card γ < N)
    {Ψ : (γ → ℝ) → (Fin N → ℝ)} (hΨ : Differentiable ℝ Ψ) :
    (volume : Measure (Fin N → ℝ)) (Set.range Ψ) = 0 := by
  rw [← Set.image_univ]
  exact volume_image_eq_zero_of_card_lt hN hcard hΨ.differentiableOn

private lemma mem_range_rrefParamMap_of_span {d m k : ℕ} (hk : 1 ≤ k)
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j)
    (hnne : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j → n i j ≠ 0)
    (hnsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hno_int : ∀ (k₁ : Fin 6) (a : Fin m), evalPoints z a ∉ interior (C k₁ : Set (Ambient d)))
    (I : Fin k → Fin d) (u : Fin k → Ambient d)
    (hI_inj : Function.Injective I)
    (hu_rref : ∀ r s : Fin k, u r (I s) = if r = s then 1 else 0)
    (hcoef : ∀ k₁ l : Fin 6, ∀ j : Fin d, n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j) :
    ∃ c : RrefConfig d m k, z ∈ Set.range (rrefParamMap c) := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  let S := nonEmptyIntParts C
  have hex_rDom : ∀ e : Pairs6, ∃ r : Fin k,
      e.1.1 ∈ S → e.1.2 ∈ S → n e.1.1 e.1.2 (I r) ≠ 0 := by
    intro e
    by_cases hmem : e.1.1 ∈ S ∧ e.1.2 ∈ S
    · have hne0 : n e.1.1 e.1.2 ≠ 0 := hnne e.1.1 hmem.1 e.1.2 hmem.2 e.2.ne
      by_contra hall
      push Not at hall
      have hzero : n e.1.1 e.1.2 = 0 := by
        apply PiLp.ext
        intro j
        rw [hcoef e.1.1 e.1.2 j]
        have hsum0 : (∑ r : Fin k, n e.1.1 e.1.2 (I r) * u r j) = 0 :=
          Finset.sum_eq_zero fun r _ => by rw [(hall r).2.2, zero_mul]
        exact hsum0
      exact hne0 hzero
    · exact ⟨⟨0, hk⟩, fun h1 h2 => False.elim (hmem ⟨h1, h2⟩)⟩
  choose rDom hrDom_spec using hex_rDom
  have hex_sig : ∀ a : Fin m,
      ∃ e : Pairs6, e.1.1 ∈ S ∧ e.1.2 ∈ S ∧ ⟪n e.1.1 e.1.2, p a⟫_ℝ = 0 := by
    intro a
    obtain ⟨i, hiS, j, hjS, hij, hzero⟩ :=
      skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
        (fun q hq => hno_int q a hq)
    exact ⟨⟨(i, j), hij⟩, hiS, hjS, hzero⟩
  choose σ hσ1 hσ2 hσ_zero using hex_sig
  let cfg : RrefConfig d m k := ⟨⟨I, hI_inj⟩, rDom, σ⟩
  let cCoef : Pairs6 → Fin k → ℝ := fun e r =>
    if e.1.1 ∈ S ∧ e.1.2 ∈ S then
      (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r)
    else if r = rDom e then 1 else 0
  have hc_dom : ∀ e : Pairs6, cCoef e (rDom e) = 1 := fun e => by
    dsimp [cCoef]
    by_cases h : e.1.1 ∈ S ∧ e.1.2 ∈ S
    · simp [h, inv_mul_cancel₀ (hrDom_spec e h.1 h.2)]
    · simp [h]
  let y : RrefParamIdx cfg.I.1 cfg.rDom cfg.σ → ℝ
    | Sum.inl (r, j) => u r j.1
    | Sum.inr (Sum.inl ⟨e, r⟩) => cCoef e r.1
    | Sum.inr (Sum.inr ⟨a, j⟩) => p a j.1
  have hy_U : ∀ r j, rrefParamU cfg y r j = u r j := fun r j => by
    dsimp [rrefParamU, cfg]
    split_ifs with h1 h2
    · rw [← h1, hu_rref r r]; simp
    · obtain ⟨s, hs⟩ := h2
      have hrs : r ≠ s := fun h => h1 (h ▸ hs)
      rw [← hs, hu_rref r s]; simp [hrs]
    · rfl
  have hy_C : ∀ e r, rrefParamC cfg y e r = cCoef e r := fun e r => by
    dsimp [rrefParamC, cfg]
    split_ifs with h
    · rw [h, hc_dom e]
    · rfl
  have hy_N_perp : ∀ a : Fin m, ∑ j : Fin d, rrefParamN cfg y (σ a) j * p a j = 0 := fun a => by
    let e := σ a
    have h1 : e.1.1 ∈ S := hσ1 a
    have h2 : e.1.2 ∈ S := hσ2 a
    have hN_eq : ∀ j : Fin d, rrefParamN cfg y e j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 j := fun j => by
      dsimp [rrefParamN]
      have hc_eq : ∀ r : Fin k, rrefParamC cfg y e r =
          (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r) := fun r => by
        rw [hy_C e r]
        dsimp [cCoef]
        simp only [h1, h2, and_self, ↓reduceIte]
      simp_rw [hc_eq, hy_U]
      rw [hcoef e.1.1 e.1.2 j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hN_mul : ∀ j : Fin d, rrefParamN cfg y (σ a) j * p a j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * (n e.1.1 e.1.2 j * p a j) := fun j => by
      rw [show σ a = e from rfl, hN_eq j, mul_assoc]
    simp_rw [hN_mul]
    rw [← Finset.mul_sum]
    have hdot : ∑ j : Fin d, n e.1.1 e.1.2 j * p a j = 0 := by
      simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
        conj_trivial, mul_comm] using hσ_zero a
    rw [hdot, mul_zero]
  have hy_N_piv : ∀ e : Pairs6, rrefParamN cfg y e (I (rDom e)) = 1 := fun e => by
    dsimp [rrefParamN]
    simp_rw [hy_C, hy_U, hu_rref]
    rw [Finset.sum_eq_single (rDom e)]
    · simp [hc_dom e]
    · intro r _ hr; simp [hr]
    · intro hr; exact False.elim (hr (Finset.mem_univ _))
  refine ⟨cfg, y, ?_⟩
  funext x
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [rrefParamMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = I (rDom (σ a)) := hj
    have hp0_eq : ∀ q : Fin d, rrefParamP0 cfg y a q =
        if q = I (rDom (σ a)) then 0 else p a q := fun q => by
      dsimp [rrefParamP0, cfg]
      split_ifs <;> rfl
    simp_rw [hp0_eq]
    have hsplit : ∑ q : Fin d, rrefParamN cfg y (σ a) q * (if q = I (rDom (σ a)) then 0 else p a q) =
        (∑ q ∈ Finset.univ.erase (I (rDom (σ a))), rrefParamN cfg y (σ a) q * p a q) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (I (rDom (σ a))))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [(Finset.mem_erase.mp hq).1]
    have hsplit_full : ∑ q : Fin d, rrefParamN cfg y (σ a) q * p a q =
        rrefParamN cfg y (σ a) (I (rDom (σ a))) * p a (I (rDom (σ a))) +
          ∑ q ∈ Finset.univ.erase (I (rDom (σ a))), rrefParamN cfg y (σ a) q * p a q :=
      (Finset.add_sum_erase Finset.univ (fun q => rrefParamN cfg y (σ a) q * p a q)
        (Finset.mem_univ (I (rDom (σ a))))).symm
    rw [hy_N_perp a, hy_N_piv (σ a), one_mul] at hsplit_full
    have hpj : p a (I (rDom (σ a))) = p a j := by rw [← hj_eq]
    change - ∑ q : Fin d, rrefParamN cfg y (σ a) q * (if q = I (rDom (σ a)) then 0 else p a q) =
      z (finProdFinEquiv (a, j))
    rw [hsplit]
    linarith [hsplit_full, hpj, hp_eq]
  · have hj_ne : j ≠ I (rDom (σ a)) := hj
    dsimp [rrefParamP0, cfg, y]
    simp [hj_ne, hp_eq]

/-- Unconditional existence of `5 * d + 36` central blocking points in `unitBall d` (`d ≥ 5`). -/
theorem exists_isBlocking (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : Fin (5 * d + 36) → Ambient d, IsBlocking p := by
  let m := 5 * d + 36
  have hmd : 0 < m * d := by positivity
  let bad : Set (Fin (m * d) → ℝ) := ⋃ c : RrefConfig d m 5, Set.range (rrefParamMap c)
  have hbad_vol : (volume : Measure (Fin (m * d) → ℝ)) bad = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (RrefParamIdx c.I.1 c.rDom c.σ) < m * d := by
      rw [card_rrefParamIdx c]
      have hm_prod : m * d = m * (d - 1) + m := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        ring
      rw [hm_prod]
      dsimp [m]
      omega
    exact volume_range_eq_zero_of_card_lt hmd hcard (differentiable_rrefParamMap c)
  let good : Set (Fin (m * d) → ℝ) :=
    {z | ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1}
  have hgood_open : IsOpen good := by
    have heq : good = ⋂ a : Fin m, (fun z => evalPoints z a) ⁻¹' Metric.ball (0 : Ambient d) 1 := by
      ext z; simp [good]
    rw [heq]
    refine isOpen_iInter_of_finite fun a => Metric.isOpen_ball.preimage ?_
    exact (continuous_apply a).comp continuous_evalPoints
  have hzero_good : (0 : Fin (m * d) → ℝ) ∈ good := fun a => by
    have hev : evalPoints (0 : Fin (m * d) → ℝ) a = 0 := by
      apply PiLp.ext
      intro j
      rfl
    rw [hev]
    exact Metric.mem_ball_self zero_lt_one
  have hgood_pos : 0 < (volume : Measure (Fin (m * d) → ℝ)) good :=
    hgood_open.measure_pos volume ⟨0, hzero_good⟩
  have hnot_sub : ¬ good ⊆ bad := fun hsub => by
    have hle : (volume : Measure (Fin (m * d) → ℝ)) good ≤ volume bad := measure_mono hsub
    rw [hbad_vol] at hle
    exact (lt_of_lt_of_le hgood_pos hle).ne' rfl
  obtain ⟨z, hz_good, hz_not_bad⟩ := Set.not_subset.mp hnot_sub
  refine ⟨evalPoints z, ?_⟩
  by_contra hnot_block
  dsimp [IsBlocking] at hnot_block
  push Not at hnot_block
  obtain ⟨C, hcov, hdisj, h0, hno_int⟩ := hnot_block
  obtain ⟨n, I, u, hI_inj, hu_rref, _hnii, hnsym, _hnnotS, hnne, hnsep, hcoef⟩ :=
    separating_normals_in_rref_span hd C hcov hdisj h0
  obtain ⟨c, hc⟩ := mem_range_rrefParamMap_of_span (by norm_num : 1 ≤ 5) z hz_good C hcov n
    hnsym hnne hnsep hno_int I u hI_inj hu_rref hcoef
  exact hz_not_bad (Set.mem_iUnion.mpr ⟨c, hc⟩)

private lemma separating_normals_rref_of_a_span {d k : ℕ} (hk : k ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_nn : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hnsym : ∀ i j, n j i = - n i j)
    (A : Fin k → Ambient d)
    (ha_span_A : ∀ i : Fin 6, (∑ j : Fin 6, n i j) ∈ Submodule.span ℝ (Set.range A)) :
    ∃ (I : Fin k → Fin d) (u : Fin k → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin k, u r (I s) = if r = s then 1 else 0) ∧
      (∀ k₁ l : Fin 6, ∀ j : Fin d,
        n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  obtain ⟨I, u, hI_inj, hu_rref, hA_span⟩ := exists_rref k hk A
  have hA_le_u : Submodule.span ℝ (Set.range A) ≤ Submodule.span ℝ (Set.range u) :=
    Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hA_span t)
  have ha_span : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range u) := fun i =>
    hA_le_u (ha_span_A i)
  have hinner_single : ∀ (w : Ambient d) (j : Fin d),
      ⟪w, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = w j := fun w j => by
    rw [EuclideanSpace.inner_single_right, one_mul]
    simp
  have hspan_perp : ∀ {v : Ambient d},
      (∀ r : Fin k, ⟪u r, v⟫_ℝ = 0) →
      ∀ i : Fin 6, ⟪a i, v⟫_ℝ = 0 := by
    intro v hv i
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (ha_span i)
    · rintro _ ⟨r, rfl⟩; exact hv r
    · simp
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [real_inner_smul_left, hx, mul_zero]
  have hcoef : ∀ k₁ l : Fin 6, ∀ j : Fin d,
      n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j := by
    intro k₁ l j
    let v : Ambient d :=
      EuclideanSpace.single j (1 : ℝ) -
        ∑ r : Fin k, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)
    have hv_u : ∀ s : Fin k, ⟪u s, v⟫_ℝ = 0 := fun s => by
      dsimp [v]
      rw [inner_sub_right, inner_sum, hinner_single]
      have hsum : (∑ r : Fin k, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) = u s j := by
        calc ∑ r : Fin k, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ
            = ∑ r : Fin k, u r j * u s (I r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [real_inner_smul_right, hinner_single]
          _ = ∑ r : Fin k, u r j * (if s = r then 1 else 0) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_rref s r]
          _ = u s j := by simp
      rw [hsum, sub_self]
    have hv_n : ⟪n k₁ l, v⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS hsep_nn hnsym (hspan_perp hv_u) k₁ l
    dsimp [v] at hv_n
    rw [inner_sub_right, inner_sum, hinner_single] at hv_n
    have hsum_n :
        (∑ r : Fin k, ⟪n k₁ l, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) =
          ∑ r : Fin k, n k₁ l (I r) * u r j := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [real_inner_smul_right, hinner_single, mul_comm]
    linarith [hv_n, hsum_n]
  exact ⟨I, u, hI_inj, hu_rref, hcoef⟩

private lemma normal_row_sum_zero {d : ℕ} (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j) :
    ∑ i : Fin 6, ∑ j : Fin 6, n i j = 0 := by
  have hneg : (∑ i : Fin 6, ∑ j : Fin 6, n i j) = - ∑ i : Fin 6, ∑ j : Fin 6, n i j := by
    calc ∑ i : Fin 6, ∑ j : Fin 6, n i j
        = ∑ j : Fin 6, ∑ i : Fin 6, n i j := Finset.sum_comm
      _ = ∑ j : Fin 6, ∑ i : Fin 6, (- n j i) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hnsym j i]
      _ = - ∑ j : Fin 6, ∑ i : Fin 6, n j i := by
        simp [Finset.sum_neg_distrib]
  have hadd : (∑ i : Fin 6, ∑ j : Fin 6, n i j) + (∑ i : Fin 6, ∑ j : Fin 6, n i j) = 0 := by
    conv_lhs => rhs; rw [hneg]
    exact add_neg_cancel _
  have h2 : (2 : ℝ) • (∑ i : Fin 6, ∑ j : Fin 6, n i j) = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma separating_normals_in_rref4_span {d : ℕ} (hd : 4 ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_nn : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hnsym : ∀ i j, n j i = - n i j)
    (hnot_indep : ¬ LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) :
    ∃ (I : Fin 4 → Fin d) (u : Fin 4 → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin 4, u r (I s) = if r = s then 1 else 0) ∧
      (∀ k₁ l : Fin 6, ∀ j : Fin d,
        n k₁ l j = ∑ r : Fin 4, n k₁ l (I r) * u r j) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := normal_row_sum_zero n hnsym
  obtain ⟨c, hc_sum, t₀, hct₀⟩ := Fintype.not_linearIndependent_iff.mp hnot_indep
  let A' : Fin 4 → Ambient d := fun r => a (t₀.succAbove r).succ
  have ha_span_A' : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range A') := by
    have hsuccAbove_mem : ∀ r : Fin 4, a (t₀.succAbove r).succ ∈ Submodule.span ℝ (Set.range A') :=
      fun r => Submodule.subset_span ⟨r, rfl⟩
    have ht₀_mem : a t₀.succ ∈ Submodule.span ℝ (Set.range A') := by
      have hsplit :
          c t₀ • a t₀.succ + ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ = 0 := by
        rw [← Fin.sum_univ_succAbove (fun t : Fin 5 => c t • a t.succ) t₀]
        exact hc_sum
      have hneg :
          c t₀ • a t₀.succ = - ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ :=
        eq_neg_of_add_eq_zero_left hsplit
      have hinv :
          a t₀.succ = -(c t₀)⁻¹ • ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ := by
        have h1 := congrArg ((c t₀)⁻¹ • ·) hneg
        rw [smul_smul, inv_mul_cancel₀ hct₀, one_smul] at h1
        rw [h1, smul_neg, neg_smul]
      rw [hinv]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun r _ => ?_)
      exact Submodule.smul_mem _ _ (hsuccAbove_mem r)
    have hsucc_mem : ∀ t : Fin 5, a t.succ ∈ Submodule.span ℝ (Set.range A') := fun t => by
      by_cases ht : t = t₀
      · subst ht; exact ht₀_mem
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq ht
        exact hsuccAbove_mem r
    intro i
    refine Fin.cases ?_ hsucc_mem i
    have ha0 : a 0 = - ∑ t : Fin 5, a t.succ := by
      have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
        simpa only [← Fin.sum_univ_succ] using ha_sum0
      exact eq_neg_of_add_eq_zero_left hsplit
    rw [ha0]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ => hsucc_mem t)
  exact separating_normals_rref_of_a_span hd C hcov n hnnotS hsep_nn hnsym A' ha_span_A'

private lemma exists_vec_inner_eq {d : ℕ}
    (a : Fin 6 → Ambient d) (ha_sum0 : ∑ i : Fin 6, a i = 0)
    (hindep : LinearIndependent ℝ (fun t : Fin 5 => a t.succ))
    (y : Fin 6 → ℝ) (hy : ∑ i : Fin 6, y i = 0) :
    ∃ x : Ambient d, ∀ i : Fin 6, ⟪a i, x⟫_ℝ = y i := by
  let Φ : Ambient d →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin 5) ℝ).symm (fun t => ⟪a t.succ, x⟫_ℝ)
      map_add' := fun x₁ x₂ => by
        ext t
        change ⟪a t.succ, x₁ + x₂⟫_ℝ = ⟪a t.succ, x₁⟫_ℝ + ⟪a t.succ, x₂⟫_ℝ
        exact inner_add_right _ _ _
      map_smul' := fun r x => by
        ext t
        change ⟪a t.succ, r • x⟫_ℝ = r * ⟪a t.succ, x⟫_ℝ
        exact real_inner_smul_right _ _ _ }
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    let v : Ambient d := ∑ t : Fin 5, z t • a t.succ
    have hz_perp : ⟪Φ v, z⟫_ℝ = 0 := hz (Φ v) ⟨v, rfl⟩
    have hinner : ⟪Φ v, z⟫_ℝ = ⟪v, v⟫_ℝ := by
      have h1 : ⟪Φ v, z⟫_ℝ = ∑ t : Fin 5, z t * ⟪a t.succ, v⟫_ℝ := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
        rfl
      have h2 : ⟪v, v⟫_ℝ = ∑ t : Fin 5, z t * ⟪a t.succ, v⟫_ℝ := by
        dsimp [v]
        rw [sum_inner]
        refine Finset.sum_congr rfl fun t _ => real_inner_smul_left _ _ _
      exact h1.trans h2.symm
    rw [hinner, inner_self_eq_zero] at hz_perp
    have hz_coef : ∀ t : Fin 5, z t = 0 :=
      (Fintype.linearIndependent_iff.mp hindep) z hz_perp
    exact PiLp.ext hz_coef
  let y' : EuclideanSpace ℝ (Fin 5) := (EuclideanSpace.equiv (Fin 5) ℝ).symm (fun t => y t.succ)
  have hy'_mem : y' ∈ LinearMap.range Φ := hrange ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hy'_mem
  refine ⟨x, fun i => ?_⟩
  have hsucc : ∀ t : Fin 5, ⟪a t.succ, x⟫_ℝ = y t.succ := fun t => by
    have ht := congrArg (fun w : EuclideanSpace ℝ (Fin 5) => w t) hx
    simpa [Φ, y'] using ht
  refine Fin.cases ?_ hsucc i
  have ha0 : a 0 = - ∑ t : Fin 5, a t.succ := by
    have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
      simpa only [← Fin.sum_univ_succ] using ha_sum0
    exact eq_neg_of_add_eq_zero_left hsplit
  have hy0 : y 0 = - ∑ t : Fin 5, y t.succ := by
    have hsplit : y 0 + ∑ t : Fin 5, y t.succ = 0 := by
      simpa only [← Fin.sum_univ_succ] using hy
    exact eq_neg_of_add_eq_zero_left hsplit
  rw [ha0, hy0, inner_neg_left, sum_inner]
  congr 1
  exact Finset.sum_congr rfl fun t _ => hsucc t

private lemma hyperplane_miss_orthants_eq_zero {b : EuclideanSpace ℝ (Fin 3)} (hb : b ≠ 0)
    (β : ℝ)
    (hpos : ∀ z : EuclideanSpace ℝ (Fin 3), (∀ r : Fin 3, 0 < z r) → ⟪b, z⟫_ℝ ≠ β)
    (hneg : ∀ z : EuclideanSpace ℝ (Fin 3), (∀ r : Fin 3, z r < 0) → ⟪b, z⟫_ℝ ≠ β) :
    β = 0 := by
  by_contra hβ
  have himp : ∀ (z : Fin 3 → ℝ),
      ⟪b, (EuclideanSpace.equiv (Fin 3) ℝ).symm z⟫_ℝ = ∑ r : Fin 3, b r * z r := fun z => by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, mul_comm]
    rfl
  by_cases hmix : ∃ p q : Fin 3, 0 < b p ∧ b q < 0
  · obtain ⟨p, q, hbp, hbq⟩ := hmix
    let z₁ : Fin 3 → ℝ := fun _ => 1
    let s₁ := ∑ r : Fin 3, b r * z₁ r
    rcases lt_trichotomy s₁ β with hs1 | hs1 | hs1
    · let z : Fin 3 → ℝ := fun j => if j = p then 1 + (β - s₁) / b p else 1
      have hz_pos : ∀ r : Fin 3, 0 < z r := fun r => by
        dsimp [z]
        split_ifs
        · have hdiv : 0 < (β - s₁) / b p := div_pos (by linarith) hbp
          linarith
        · norm_num
      apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z) hz_pos
      rw [himp]
      have hp_term : b p * z p = b p * 1 + (β - s₁) := by
        dsimp [z]
        simp only [↓reduceIte]
        field_simp [hbp.ne']
      have hdiff : ∑ r : Fin 3, b r * z r = ∑ r : Fin 3, b r * z₁ r + (β - s₁) := by
        rw [← Finset.add_sum_erase Finset.univ (fun r => b r * z r) (Finset.mem_univ p),
            ← Finset.add_sum_erase Finset.univ (fun r => b r * z₁ r) (Finset.mem_univ p)]
        have hrest : ∑ r ∈ Finset.univ.erase p, b r * z r = ∑ r ∈ Finset.univ.erase p, b r * z₁ r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
          simp [z, z₁, hrp]
        rw [hrest, hp_term]
        dsimp [z₁]
        ring
      rw [hdiff]
      dsimp [s₁]
      ring
    · apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z₁) (fun _ => by norm_num)
      rw [himp]
      exact hs1
    · let z : Fin 3 → ℝ := fun j => if j = q then 1 + (β - s₁) / b q else 1
      have hz_pos : ∀ r : Fin 3, 0 < z r := fun r => by
        dsimp [z]
        split_ifs
        · have hdiv : 0 < (β - s₁) / b q := div_pos_of_neg_of_neg (by linarith) hbq
          linarith
        · norm_num
      apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z) hz_pos
      rw [himp]
      have hq_term : b q * z q = b q * 1 + (β - s₁) := by
        dsimp [z]
        simp only [↓reduceIte]
        field_simp [hbq.ne]
      have hdiff : ∑ r : Fin 3, b r * z r = ∑ r : Fin 3, b r * z₁ r + (β - s₁) := by
        rw [← Finset.add_sum_erase Finset.univ (fun r => b r * z r) (Finset.mem_univ q),
            ← Finset.add_sum_erase Finset.univ (fun r => b r * z₁ r) (Finset.mem_univ q)]
        have hrest : ∑ r ∈ Finset.univ.erase q, b r * z r = ∑ r ∈ Finset.univ.erase q, b r * z₁ r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
          simp [z, z₁, hrq]
        rw [hrest, hq_term]
        dsimp [z₁]
        ring
      rw [hdiff]
      dsimp [s₁]
      ring
  · have h_same : (∀ r : Fin 3, 0 ≤ b r) ∨ (∀ r : Fin 3, b r ≤ 0) := by
      by_cases hex_pos : ∃ p : Fin 3, 0 < b p
      · left
        obtain ⟨p, hbp⟩ := hex_pos
        intro q
        exact le_of_not_gt fun hbq => hmix ⟨p, q, hbp, hbq⟩
      · right
        push Not at hex_pos
        exact hex_pos
    have hex_ne : ∃ r : Fin 3, b r ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hb (PiLp.ext hall)
    let s := ∑ r : Fin 3, b r
    have hs_ne : s ≠ 0 := by
      obtain ⟨r₀, hr₀⟩ := hex_ne
      rcases h_same with hnn | hnp
      · have hpos_r : 0 < b r₀ := lt_of_le_of_ne (hnn r₀) hr₀.symm
        have hge : b r₀ ≤ s := Finset.single_le_sum (fun r _ => hnn r) (Finset.mem_univ r₀)
        linarith
      · have hneg_r : b r₀ < 0 := lt_of_le_of_ne (hnp r₀) hr₀
        have hle : s ≤ b r₀ := by
          have h := Finset.single_le_sum (fun r _ => neg_nonneg.mpr (hnp r)) (Finset.mem_univ r₀)
          simp only [Finset.sum_neg_distrib] at h
          linarith
        linarith
    let t := β / s
    have ht_ne : t ≠ 0 := div_ne_zero hβ hs_ne
    let z : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm fun _ => t
    have hdot : ⟪b, z⟫_ℝ = β := by
      rw [himp, ← Finset.sum_mul]
      change s * (β / s) = β
      exact mul_div_cancel₀ β hs_ne
    rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos
    · exact hneg z (fun _ => ht_neg) hdot
    · exact hpos z (fun _ => ht_pos) hdot

private lemma rank5_triangle_dependent {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_all : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0) ∧
      (∀ x ∈ interior (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ < 0))
    (hnsym : ∀ i j, n j i = - n i j)
    (hindep : LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) :
    (nonEmptyIntParts C = Finset.univ) ∧
    (∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
      ∃ c₁ c₂ c₃ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
        c₁ • n i j + c₂ • n j k + c₃ • n k i = 0) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := normal_row_sum_zero n hnsym
  have hS_univ : nonEmptyIntParts C = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    by_contra hiS
    have hai0 : a i = 0 := Finset.sum_eq_zero fun j _ => hnnotS i j (Or.inl hiS)
    refine Fin.cases (fun hi0 => ?_) (fun t ht0 => ?_) i hai0
    · have hsum0 : ∑ t : Fin 5, (1 : ℝ) • a t.succ = 0 := by
        simp only [one_smul]
        have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
          simpa only [← Fin.sum_univ_succ] using ha_sum0
        rw [hi0, zero_add] at hsplit
        exact hsplit
      have h10 := (Fintype.linearIndependent_iff.mp hindep) (fun _ => 1) hsum0 0
      norm_num at h10
    · exact (hindep.ne_zero t) ht0
  have hinner_a_ge : ∀ (l : Fin 6) {y : Ambient d}, y ∈ (C l : Set (Ambient d)) → 0 ≤ ⟪a l, y⟫_ℝ := by
    intro l y hy
    dsimp [a]
    rw [sum_inner]
    refine Finset.sum_nonneg fun q _ => ?_
    by_cases hql : l = q
    · subst hql
      have hadd : n l l + n l l = 0 := by
        conv_lhs => rhs; rw [hnsym l l]
        exact add_neg_cancel _
      have h2 : (2 : ℝ) • n l l = 0 := by rwa [two_smul]
      rw [(smul_eq_zero.mp h2).resolve_left two_ne_zero, inner_zero_left]
    · exact (hsep_all l (hS_univ ▸ Finset.mem_univ l) q (hS_univ ▸ Finset.mem_univ q) hql).1 y hy
  have hpos_of_other_neg : ∀ (p : Fin 6) {x : Ambient d},
      (∀ l : Fin 6, l ≠ p → ⟪a l, x⟫_ℝ < 0) →
      ∀ q : Fin 6, q ≠ p → 0 < ⟪n p q, x⟫_ℝ := by
    intro p x hneg q hqp
    let α : ℝ := (2 * (‖x‖ + 1))⁻¹
    have hα_pos : 0 < α := inv_pos.mpr (by positivity)
    let z : Ambient d := α • x
    have hz_ball : z ∈ Metric.ball (0 : Ambient d) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [z]
      rw [norm_smul, Real.norm_of_nonneg hα_pos.le]
      dsimp [α]
      have hden : 0 < 2 * (‖x‖ + 1) := by positivity
      rw [inv_mul_lt_one₀ hden]
      linarith [norm_nonneg x]
    let U : Set (Ambient d) :=
      Metric.ball (0 : Ambient d) 1 ∩ ⋂ l ∈ Finset.univ.erase p, {y : Ambient d | ⟪a l, y⟫_ℝ < 0}
    have hU_open : IsOpen U :=
      Metric.isOpen_ball.inter <| isOpen_biInter_finset fun l _ =>
        isOpen_lt (continuous_const.inner continuous_id) continuous_const
    have hz_U : z ∈ U := by
      refine ⟨hz_ball, Set.mem_iInter₂.mpr fun l hl => ?_⟩
      have hlp : l ≠ p := (Finset.mem_erase.mp hl).1
      change ⟪a l, α • x⟫_ℝ < 0
      rw [real_inner_smul_right]
      exact mul_neg_of_pos_of_neg hα_pos (hneg l hlp)
    have hU_sub : U ⊆ (C p : Set (Ambient d)) := by
      intro y hyU
      have hy_ball : y ∈ unitBall d := Metric.ball_subset_closedBall hyU.1
      rw [hcov] at hy_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hy_ball
      by_cases hlp : l = p
      · exact hlp ▸ hl
      · have hle := hinner_a_ge l hl
        have hlt : ⟪a l, y⟫_ℝ < 0 :=
          Set.mem_iInter₂.mp hyU.2 l (Finset.mem_erase.mpr ⟨hlp, Finset.mem_univ l⟩)
        exact False.elim (not_lt_of_ge hle hlt)
    have hz_int : z ∈ interior (C p : Set (Ambient d)) := interior_maximal hU_sub hU_open hz_U
    have hz_pos : 0 < ⟪n p q, z⟫_ℝ :=
      (hsep_all p (hS_univ ▸ Finset.mem_univ p) q (hS_univ ▸ Finset.mem_univ q) hqp.symm).2.1 z hz_int
    dsimp [z] at hz_pos
    rw [real_inner_smul_right] at hz_pos
    exact pos_of_mul_pos_right hz_pos hα_pos.le
  refine ⟨hS_univ, fun i j k hij hjk hik => ?_⟩
  let M₀ : Finset (Fin 6) := Finset.univ.filter fun m => m ≠ i ∧ m ≠ j ∧ m ≠ k
  have hM₀_card : M₀.card = 3 := by
    have heq : M₀ = Finset.univ \ ({i, j, k} : Finset (Fin 6)) := by
      ext m; simp [M₀, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
    have h3 : ({i, j, k} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hjk]
      · simp [hij, hik]
    omega
  have hex_x0 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = i ∨ l = j ∨ l = k then 1 else -1) (by
      have hsplit : (∑ l : Fin 6, if l = i ∨ l = j ∨ l = k then (1 : ℝ) else -1) =
          ∑ l ∈ ({i, j, k} : Finset (Fin 6)), (1 : ℝ) + ∑ l ∈ M₀, (-1 : ℝ) := by
        have hdisj : Disjoint ({i, j, k} : Finset (Fin 6)) M₀ := by
          rw [Finset.disjoint_left]
          intro l hl hlM
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hlM
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          tauto
        have hun : ({i, j, k} : Finset (Fin 6)) ∪ M₀ = Finset.univ := by
          ext l
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, M₀,
            Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          tauto
        rw [← hun, Finset.sum_union hdisj]
        congr 1
        · refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          simp [hl]
        · refine Finset.sum_congr rfl fun l hl => ?_
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          simp [hl.1, hl.2.1, hl.2.2]
      have h3 : ({i, j, k} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hjk]
        · simp [hij, hik]
      rw [hsplit, Finset.sum_const, Finset.sum_const, h3, hM₀_card]
      norm_num)
  obtain ⟨x₀, hx₀⟩ := hex_x0
  have hex_w1 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = i then 1 else if l = k then -1 else 0) (by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [↓reduceIte]
      have hk_mem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
      rw [← Finset.add_sum_erase _ _ hk_mem]
      simp only [hik.symm, ↓reduceIte]
      have hrest : (∑ l ∈ (Finset.univ.erase i).erase k,
          if l = i then (1 : ℝ) else if l = k then -1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [hli, hlk]
      rw [hrest]; ring)
  obtain ⟨w₁, hw₁⟩ := hex_w1
  have hex_w2 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = j then 1 else if l = k then -1 else 0) (by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
      simp only [↓reduceIte]
      have hk_mem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
      rw [← Finset.add_sum_erase _ _ hk_mem]
      simp only [hjk.symm, ↓reduceIte]
      have hrest : (∑ l ∈ (Finset.univ.erase j).erase k,
          if l = j then (1 : ℝ) else if l = k then -1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [hlj, hlk]
      rw [hrest]; ring)
  obtain ⟨w₂, hw₂⟩ := hex_w2
  have hex_e : ∀ m ∈ M₀, ∃ em : Ambient d, ∀ l : Fin 6,
      ⟪a l, em⟫_ℝ = if l = m then -1 else if l = i then 1 else 0 := by
    intro m hm
    have hmi : m ≠ i := (Finset.mem_filter.mp hm).2.1
    refine exists_vec_inner_eq a ha_sum0 hindep
      (fun l => if l = m then -1 else if l = i then 1 else 0) ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m)]
    simp only [↓reduceIte]
    have hi_mem : i ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hmi.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hi_mem]
    simp only [hmi.symm, ↓reduceIte]
    have hrest : (∑ l ∈ (Finset.univ.erase m).erase i,
        if l = m then (-1 : ℝ) else if l = i then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hli := (Finset.mem_erase.mp hl).1
      have hlm := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      simp [hlm, hli]
    rw [hrest]; ring
  choose eOf heOf using hex_e
  let T : Ambient d →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![⟪n i j, x⟫_ℝ, ⟪n j k, x⟫_ℝ, ⟪n k i, x⟫_ℝ]
      map_add' := fun x y => by
        ext r
        fin_cases r <;> exact inner_add_right _ _ _
      map_smul' := fun r x => by
        ext q
        fin_cases q <;> exact real_inner_smul_right _ _ _ }
  let uI : Ambient d := (2 : ℝ) • w₁ - w₂
  let uJ : Ambient d := -w₁ + (2 : ℝ) • w₂
  let uK : Ambient d := -w₁ - w₂
  have hx₀_l : ∀ l : Fin 6, l ∉ ({i, j, k} : Finset (Fin 6)) → ⟪a l, x₀⟫_ℝ = -1 := fun l hl => by
    rw [hx₀ l]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    simp [hl]
  have hw_m : ∀ l : Fin 6, l ∉ ({i, j, k} : Finset (Fin 6)) → ⟪a l, w₁⟫_ℝ = 0 ∧ ⟪a l, w₂⟫_ℝ = 0 :=
    fun l hl => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    push Not at hl
    rw [hw₁ l, hw₂ l]
    simp [hl.1, hl.2.1, hl.2.2]
  have hcone_I : ∀ (α β : ℝ), 0 < α → β < 0 → 0 < α + β →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → 0 ≤ T v 0 ∧ T v 2 ≤ 0 := by
    intro α β hα hβ hαβ v hv
    have hneg_t : ∀ t : ℝ, 2 / α < t → 2 / (-β) < t → 2 / (α + β) < t →
        ∀ l : Fin 6, l ≠ i → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 ht3 l hli
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_j : l = j
      · rw [hl_j]
        have hvj : ⟪a j, v⟫_ℝ = β := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
            hw₁ j, hw₂ j]
          simp [hij.symm, hjk]
        have hx0j : ⟪a j, x₀⟫_ℝ = 1 := by simp [hx₀ j]
        rw [hx0j, hvj]
        have hlt : 2 < t * (-β) := (div_lt_iff₀ (by linarith)).mp ht2
        linarith
      · by_cases hl_k : l = k
        · rw [hl_k]
          have hvk : ⟪a k, v⟫_ℝ = -(α + β) := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              hw₁ k, hw₂ k]
            simp [hik.symm, hjk.symm]
            ring
          have hx0k : ⟪a k, x₀⟫_ℝ = 1 := by simp [hx₀ k]
          rw [hx0k, hvk]
          have hlt : 2 < t * (α + β) := (div_lt_iff₀ hαβ).mp ht3
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hl_j, hl_k]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]
            ring
          rw [hx₀_l l hl_not, hvm]
          linarith
    have hall_t : ∀ t : ℝ, max (2 / α) (max (2 / (-β)) (2 / (α + β))) < t →
        0 < T (x₀ + t • v) 0 ∧ T (x₀ + t • v) 2 < 0 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) ht)
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) ht)
      have h1 := hpos_of_other_neg i hnt j hij.symm
      have h2 := hpos_of_other_neg i hnt k hik.symm
      have h2' : ⟪n k i, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym i k, inner_neg_left]; linarith
      exact ⟨h1, h2'⟩
    have hT0 : 0 ≤ T v 0 := by
      by_contra hv0
      push Not at hv0
      let M := max (max (2 / α) (max (2 / (-β)) (2 / (α + β)))) ((|T x₀ 0| + 1) / (-T v 0))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hgt : (|T x₀ 0| + 1) / (-T v 0) < M + 1 :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one M)
      have hmul : |T x₀ 0| + 1 < (M + 1) * (-T v 0) := (div_lt_iff₀ (by linarith)).mp hgt
      have hlin : T (x₀ + (M + 1) • v) 0 = T x₀ 0 + (M + 1) * T v 0 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 0 ≤ |T x₀ 0| := le_abs_self _
      linarith [ht.1]
    have hT2 : T v 2 ≤ 0 := by
      by_contra hv2
      push Not at hv2
      let M := max (max (2 / α) (max (2 / (-β)) (2 / (α + β)))) ((|T x₀ 2| + 1) / (T v 2))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hgt : (|T x₀ 2| + 1) / T v 2 < M + 1 :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one M)
      have hmul : |T x₀ 2| + 1 < (M + 1) * T v 2 := (div_lt_iff₀ hv2).mp hgt
      have hlin : T (x₀ + (M + 1) • v) 2 = T x₀ 2 + (M + 1) * T v 2 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 2 ≤ |T x₀ 2| := neg_le_abs _
      linarith [ht.2]
    exact ⟨hT0, hT2⟩
  have hcone_J : ∀ (α β : ℝ), α < 0 → 0 < β → 0 < α + β →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → T v 0 ≤ 0 ∧ 0 ≤ T v 1 := by
    intro α β hα hβ hαβ v hv
    have hneg_t : ∀ t : ℝ, 2 / (-α) < t → 2 / β < t → 2 / (α + β) < t →
        ∀ l : Fin 6, l ≠ j → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 ht3 l hlj
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_i : l = i
      · rw [hl_i]
        have hvi : ⟪a i, v⟫_ℝ = α := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
          simp [hij, hik]
        have hx0i : ⟪a i, x₀⟫_ℝ = 1 := by simp [hx₀ i]
        rw [hx0i, hvi]
        have hlt : 2 < t * (-α) := (div_lt_iff₀ (by linarith)).mp ht1
        linarith
      · by_cases hl_k : l = k
        · rw [hl_k]
          have hvk : ⟪a k, v⟫_ℝ = -(α + β) := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ k, hw₂ k]
            simp [hik.symm, hjk.symm]; ring
          have hx0k : ⟪a k, x₀⟫_ℝ = 1 := by simp [hx₀ k]
          rw [hx0k, hvk]
          have hlt : 2 < t * (α + β) := (div_lt_iff₀ hαβ).mp ht3
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hl_i, hlj, hl_k]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]; ring
          rw [hx₀_l l hl_not, hvm]; linarith
    have hall_t : ∀ t : ℝ, max (2 / (-α)) (max (2 / β) (2 / (α + β))) < t →
        T (x₀ + t • v) 0 < 0 ∧ 0 < T (x₀ + t • v) 1 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) ht)
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) ht)
      have h1 := hpos_of_other_neg j hnt i hij
      have h2 := hpos_of_other_neg j hnt k hjk.symm
      have h1' : ⟪n i j, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym j i, inner_neg_left]; linarith
      exact ⟨h1', h2⟩
    have hT0 : T v 0 ≤ 0 := by
      by_contra hv0
      push Not at hv0
      let M := max (max (2 / (-α)) (max (2 / β) (2 / (α + β)))) ((|T x₀ 0| + 1) / (T v 0))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 0| + 1 < (M + 1) * T v 0 :=
        (div_lt_iff₀ hv0).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 0 = T x₀ 0 + (M + 1) * T v 0 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 0 ≤ |T x₀ 0| := neg_le_abs _
      linarith [ht.1]
    have hT1 : 0 ≤ T v 1 := by
      by_contra hv1
      push Not at hv1
      let M := max (max (2 / (-α)) (max (2 / β) (2 / (α + β)))) ((|T x₀ 1| + 1) / (-T v 1))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 1| + 1 < (M + 1) * (-T v 1) :=
        (div_lt_iff₀ (by linarith)).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 1 = T x₀ 1 + (M + 1) * T v 1 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 1 ≤ |T x₀ 1| := le_abs_self _
      linarith [ht.2]
    exact ⟨hT0, hT1⟩
  have hcone_K : ∀ (α β : ℝ), α < 0 → β < 0 →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → T v 1 ≤ 0 ∧ 0 ≤ T v 2 := by
    intro α β hα hβ v hv
    have hneg_t : ∀ t : ℝ, 2 / (-α) < t → 2 / (-β) < t →
        ∀ l : Fin 6, l ≠ k → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 l hlk
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_i : l = i
      · rw [hl_i]
        have hvi : ⟪a i, v⟫_ℝ = α := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
          simp [hij, hik]
        have hx0i : ⟪a i, x₀⟫_ℝ = 1 := by simp [hx₀ i]
        rw [hx0i, hvi]
        have hlt : 2 < t * (-α) := (div_lt_iff₀ (by linarith)).mp ht1
        linarith
      · by_cases hl_j : l = j
        · rw [hl_j]
          have hvj : ⟪a j, v⟫_ℝ = β := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ j, hw₂ j]
            simp [hij.symm, hjk]
          have hx0j : ⟪a j, x₀⟫_ℝ = 1 := by simp [hx₀ j]
          rw [hx0j, hvj]
          have hlt : 2 < t * (-β) := (div_lt_iff₀ (by linarith)).mp ht2
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hl_i, hl_j, hlk]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]; ring
          rw [hx₀_l l hl_not, hvm]; linarith
    have hall_t : ∀ t : ℝ, max (2 / (-α)) (2 / (-β)) < t →
        T (x₀ + t • v) 1 < 0 ∧ 0 < T (x₀ + t • v) 2 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt (le_max_right _ _) ht)
      have h1 := hpos_of_other_neg k hnt j hjk
      have h2 := hpos_of_other_neg k hnt i hik
      have h1' : ⟪n j k, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym k j, inner_neg_left]; linarith
      exact ⟨h1', h2⟩
    have hT1 : T v 1 ≤ 0 := by
      by_contra hv1
      push Not at hv1
      let M := max (max (2 / (-α)) (2 / (-β))) ((|T x₀ 1| + 1) / (T v 1))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 1| + 1 < (M + 1) * T v 1 :=
        (div_lt_iff₀ hv1).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 1 = T x₀ 1 + (M + 1) * T v 1 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 1 ≤ |T x₀ 1| := neg_le_abs _
      linarith [ht.1]
    have hT2 : 0 ≤ T v 2 := by
      by_contra hv2
      push Not at hv2
      let M := max (max (2 / (-α)) (2 / (-β))) ((|T x₀ 2| + 1) / (-T v 2))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 2| + 1 < (M + 1) * (-T v 2) :=
        (div_lt_iff₀ (by linarith)).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 2 = T x₀ 2 + (M + 1) * T v 2 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 2 ≤ |T x₀ 2| := le_abs_self _
      linarith [ht.2]
    exact ⟨hT1, hT2⟩
  have hT_nz : ∀ r : Fin 3, T w₁ r ≠ 0 ∨ T w₂ r ≠ 0 := fun r => by
    by_contra hboth
    push Not at hboth
    have hzI : T uI r = 0 := by
      have h1 : T uI = (2 : ℝ) • T w₁ - T w₂ := by simp [uI, map_sub, map_smul]
      rw [h1]; simp [hboth.1, hboth.2]
    have hzJ : T uJ r = 0 := by
      have h1 : T uJ = - T w₁ + (2 : ℝ) • T w₂ := by simp [uJ, map_add, map_neg, map_smul]
      rw [h1]; simp [hboth.1, hboth.2]
    have hzK : T uK r = 0 := by
      have h1 : T uK = - T w₁ - T w₂ := by simp [uK, map_sub, map_neg]
      rw [h1]; simp [hboth.1, hboth.2]
    have huI_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uI⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (2 * ⟪a l, w₁⟫_ℝ - ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uI]
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
    have huJ_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uJ⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (-⟪a l, w₁⟫_ℝ + 2 * ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uJ]
      rw [inner_add_right, real_inner_smul_right, inner_add_right, inner_neg_right,
        real_inner_smul_right]
    have huK_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uK⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (-⟪a l, w₁⟫_ℝ - ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uK]
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, inner_neg_right]
    have hnegI : ∀ l ≠ i, ⟪a l, x₀ + (3 : ℝ) • uI⟫_ℝ < 0 := fun l hli => by
      rw [huI_a l]
      by_cases hlj : l = j
      · rw [hlj, hx₀ j, hw₁ j, hw₂ j]; simp [hij.symm, hjk]; try norm_num
      · by_cases hlk : l = k
        · rw [hlk, hx₀ k, hw₁ k, hw₂ k]; simp [hik.symm, hjk.symm]; try norm_num
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    have hnegJ : ∀ l ≠ j, ⟪a l, x₀ + (3 : ℝ) • uJ⟫_ℝ < 0 := fun l hlj => by
      rw [huJ_a l]
      by_cases hli : l = i
      · rw [hli, hx₀ i, hw₁ i, hw₂ i]; simp [hij, hik]; try norm_num
      · by_cases hlk : l = k
        · rw [hlk, hx₀ k, hw₁ k, hw₂ k]; simp [hik.symm, hjk.symm]; try norm_num
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    have hnegK : ∀ l ≠ k, ⟪a l, x₀ + (3 : ℝ) • uK⟫_ℝ < 0 := fun l hlk => by
      rw [huK_a l]
      by_cases hli : l = i
      · rw [hli, hx₀ i, hw₁ i, hw₂ i]; simp [hij, hik]
      · by_cases hlj : l = j
        · rw [hlj, hx₀ j, hw₁ j, hw₂ j]; simp [hij.symm, hjk]
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    fin_cases r
    · have hp1 : 0 < ⟪n i j, x₀ + (3 : ℝ) • uI⟫_ℝ := hpos_of_other_neg i hnegI j hij.symm
      have hp2 : ⟪n i j, x₀ + (3 : ℝ) • uJ⟫_ℝ < 0 := by
        have h := hpos_of_other_neg j hnegJ i hij
        rw [hnsym i j, inner_neg_left] at h; linarith
      have h1 : ⟪n i j, x₀⟫_ℝ = ⟪n i j, x₀ + (3 : ℝ) • uI⟫_ℝ := by
        have h : T uI 0 = 0 := hzI
        change ⟪n i j, uI⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n i j, x₀⟫_ℝ = ⟪n i j, x₀ + (3 : ℝ) • uJ⟫_ℝ := by
        have h : T uJ 0 = 0 := hzJ
        change ⟪n i j, uJ⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
    · have hp1 : 0 < ⟪n j k, x₀ + (3 : ℝ) • uJ⟫_ℝ := hpos_of_other_neg j hnegJ k hjk.symm
      have hp2 : ⟪n j k, x₀ + (3 : ℝ) • uK⟫_ℝ < 0 := by
        have h := hpos_of_other_neg k hnegK j hjk
        rw [hnsym j k, inner_neg_left] at h; linarith
      have h1 : ⟪n j k, x₀⟫_ℝ = ⟪n j k, x₀ + (3 : ℝ) • uJ⟫_ℝ := by
        have h : T uJ 1 = 0 := hzJ
        change ⟪n j k, uJ⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n j k, x₀⟫_ℝ = ⟪n j k, x₀ + (3 : ℝ) • uK⟫_ℝ := by
        have h : T uK 1 = 0 := hzK
        change ⟪n j k, uK⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
    · have hp1 : 0 < ⟪n k i, x₀ + (3 : ℝ) • uK⟫_ℝ := hpos_of_other_neg k hnegK i hik
      have hp2 : ⟪n k i, x₀ + (3 : ℝ) • uI⟫_ℝ < 0 := by
        have h := hpos_of_other_neg i hnegI k hik.symm
        rw [hnsym k i, inner_neg_left] at h; linarith
      have h1 : ⟪n k i, x₀⟫_ℝ = ⟪n k i, x₀ + (3 : ℝ) • uK⟫_ℝ := by
        have h : T uK 2 = 0 := hzK
        change ⟪n k i, uK⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n k i, x₀⟫_ℝ = ⟪n k i, x₀ + (3 : ℝ) • uI⟫_ℝ := by
        have h : T uI 2 = 0 := hzI
        change ⟪n k i, uI⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ {T w₁, T w₂}
  have hW_finrank : Module.finrank ℝ W = 2 := by
    have hle : Module.finrank ℝ W ≤ 2 := by
      have h1 : Module.finrank ℝ W ≤
          ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card :=
        finrank_span_le_card ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3)))
      have h2 : ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card ≤ 2 := by
        simpa using Finset.card_le_two (a := T w₁) (b := T w₂)
      exact h1.trans h2
    have hge : 2 ≤ Module.finrank ℝ W := by
      by_contra hlt
      have hle1 : Module.finrank ℝ W ≤ 1 := by omega
      have hw1_W : T w₁ ∈ W := Submodule.subset_span (by simp)
      have hw2_W : T w₂ ∈ W := Submodule.subset_span (by simp)
      obtain ⟨v₀, hv₀, hv₀_ne⟩ : ∃ v₀ : Ambient d, (v₀ = w₁ ∨ v₀ = w₂) ∧ T v₀ 0 ≠ 0 := by
        rcases hT_nz 0 with h1 | h2
        · exact ⟨w₁, Or.inl rfl, h1⟩
        · exact ⟨w₂, Or.inr rfl, h2⟩
      have hv₀_W : T v₀ ∈ W := by rcases hv₀ with rfl | rfl <;> assumption
      have hv₀_ne0 : T v₀ ≠ 0 := fun h => hv₀_ne (by rw [h]; rfl)
      have hW_eq : W = Submodule.span ℝ {T v₀} := by
        refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀_W)
        · rw [finrank_span_singleton hv₀_ne0]; exact hle1
      have hprop : ∀ v : Ambient d, (∃ c₁ c₂ : ℝ, v = c₁ • w₁ + c₂ • w₂) →
          ∃ μ : ℝ, T v = μ • T v₀ := fun v ⟨c₁, c₂, hv⟩ => by
        have hTv_W : T v ∈ W := by
          rw [hv, map_add, map_smul, map_smul]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ hw1_W) (Submodule.smul_mem _ _ hw2_W)
        rw [hW_eq, Submodule.mem_span_singleton] at hTv_W
        exact hTv_W.imp fun μ hμ => hμ.symm
      let β := T v₀ 1 / T v₀ 0
      let γ := T v₀ 2 / T v₀ 0
      have hscale : ∀ v : Ambient d, (∃ c₁ c₂ : ℝ, v = c₁ • w₁ + c₂ • w₂) →
          T v 1 = β * T v 0 ∧ T v 2 = γ * T v 0 := fun v hv => by
        obtain ⟨μ, hμ⟩ := hprop v hv
        constructor
        · have h0 : T v 0 = μ * T v₀ 0 := by rw [hμ]; rfl
          have h1 : T v 1 = μ * T v₀ 1 := by rw [hμ]; rfl
          rw [h0, h1]; dsimp [β]; field_simp [hv₀_ne]
        · have h0 : T v 0 = μ * T v₀ 0 := by rw [hμ]; rfl
          have h2 : T v 2 = μ * T v₀ 2 := by rw [hμ]; rfl
          rw [h0, h2]; dsimp [γ]; field_simp [hv₀_ne]
      have h_no_vanish_I : 0 < T uI 0 := by
        have hge0 := (hcone_I 2 (-1) (by norm_num) (by norm_num) (by norm_num) uI
          (by dsimp [uI]; module)).1
        refine lt_of_le_of_ne hge0 (Ne.symm fun h0 => ?_)
        have hI_pert : ∀ ε : ℝ, |ε| < 1 / 4 →
            0 ≤ T (uI + ε • v₀) 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_I (2 + ε) (-1) (by linarith [abs_lt.mp hε]) (by norm_num)
              (by linarith [abs_lt.mp hε]) (uI + ε • v₀) (by dsimp [uI]; rw [hvw]; module)).1
          · exact (hcone_I 2 (-1 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (by linarith [abs_lt.mp hε]) (uI + ε • v₀) (by dsimp [uI]; rw [hvw]; module)).1
        let ε : ℝ := if T v₀ 0 > 0 then -(1 / 8) else 1 / 8
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uI + ε • v₀) 0 = T uI 0 + ε * T v₀ 0 := by
          rw [map_add, map_smul]; rfl
        have hpos_ge := hI_pert ε hε_abs
        rw [hlin, h0, zero_add] at hpos_ge
        dsimp [ε] at hpos_ge
        split_ifs at hpos_ge with hpos
        · linarith
        · have hneg : T v₀ 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv₀_ne
          linarith
      have h_no_vanish_J : T uJ 0 < 0 := by
        have hle0 := (hcone_J (-1) 2 (by norm_num) (by norm_num) (by norm_num) uJ
          (by dsimp [uJ]; module)).1
        refine lt_of_le_of_ne hle0 fun h0 => ?_
        have hJ_pert : ∀ ε : ℝ, |ε| < 1 / 4 →
            T (uJ + ε • v₀) 0 ≤ 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_J (-1 + ε) 2 (by linarith [abs_lt.mp hε]) (by norm_num)
              (by linarith [abs_lt.mp hε]) (uJ + ε • v₀) (by dsimp [uJ]; rw [hvw]; module)).1
          · exact (hcone_J (-1) (2 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (by linarith [abs_lt.mp hε]) (uJ + ε • v₀) (by dsimp [uJ]; rw [hvw]; module)).1
        let ε : ℝ := if T v₀ 0 > 0 then 1 / 8 else -(1 / 8)
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uJ + ε • v₀) 0 = T uJ 0 + ε * T v₀ 0 := by
          rw [map_add, map_smul]; rfl
        have hneg_le := hJ_pert ε hε_abs
        rw [hlin, h0, zero_add] at hneg_le
        dsimp [ε] at hneg_le
        split_ifs at hneg_le with hpos
        · linarith
        · have hneg : T v₀ 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv₀_ne
          linarith
      have hβ_ne : β ≠ 0 := by
        intro hβ0
        have hw1_1 : T w₁ 1 = 0 := by rw [(hscale w₁ ⟨1, 0, by simp⟩).1, hβ0, zero_mul]
        have hw2_1 : T w₂ 1 = 0 := by rw [(hscale w₂ ⟨0, 1, by simp⟩).1, hβ0, zero_mul]
        rcases hT_nz 1 with h | h
        · exact h hw1_1
        · exact h hw2_1
      have hγ_ne : γ ≠ 0 := by
        intro hγ0
        have hw1_2 : T w₁ 2 = 0 := by rw [(hscale w₁ ⟨1, 0, by simp⟩).2, hγ0, zero_mul]
        have hw2_2 : T w₂ 2 = 0 := by rw [(hscale w₂ ⟨0, 1, by simp⟩).2, hγ0, zero_mul]
        rcases hT_nz 2 with h | h
        · exact h hw1_2
        · exact h hw2_2
      have hK_ne0 : T uK 0 ≠ 0 := by
        intro h0
        have hK1 : T uK 1 = 0 := by rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).1, h0, mul_zero]
        have hcK1 := hK1
        have hK_pert : ∀ ε : ℝ, |ε| < 1 / 4 → T (uK + ε • v₀) 1 ≤ 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_K (-1 + ε) (-1) (by linarith [abs_lt.mp hε]) (by norm_num)
              (uK + ε • v₀) (by dsimp [uK]; rw [hvw]; module)).1
          · exact (hcone_K (-1) (-1 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (uK + ε • v₀) (by dsimp [uK]; rw [hvw]; module)).1
        have hv0_1_ne : T v₀ 1 ≠ 0 := by
          rw [(hscale v₀ (by rcases hv₀ with rfl | rfl; exact ⟨1, 0, by simp⟩; exact ⟨0, 1, by simp⟩)).1]
          exact mul_ne_zero hβ_ne hv₀_ne
        let ε : ℝ := if T v₀ 1 > 0 then 1 / 8 else -(1 / 8)
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uK + ε • v₀) 1 = T uK 1 + ε * T v₀ 1 := by
          rw [map_add, map_smul]; rfl
        have hle := hK_pert ε hε_abs
        rw [hlin, hcK1, zero_add] at hle
        dsimp [ε] at hle
        split_ifs at hle with hpos
        · linarith
        · have hneg : T v₀ 1 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv0_1_ne
          linarith
      rcases lt_or_gt_of_ne hK_ne0 with hK_neg | hK_pos
      · have hJ1 : 0 ≤ T uJ 1 := (hcone_J (-1) 2 (by norm_num) (by norm_num) (by norm_num) uJ
          (by dsimp [uJ]; module)).2
        have hK1 : T uK 1 ≤ 0 := (hcone_K (-1) (-1) (by norm_num) (by norm_num) uK
          (by dsimp [uK]; module)).1
        rw [(hscale uJ ⟨-1, 2, by dsimp [uJ]; module⟩).1] at hJ1
        rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).1] at hK1
        have hβ_le : β ≤ 0 := nonpos_of_mul_nonneg_left hJ1 h_no_vanish_J
        have hβ_ge : 0 ≤ β := nonneg_of_mul_nonpos_left hK1 hK_neg
        exact hβ_ne (le_antisymm hβ_le hβ_ge)
      · have hI2 : T uI 2 ≤ 0 := (hcone_I 2 (-1) (by norm_num) (by norm_num) (by norm_num) uI
          (by dsimp [uI]; module)).2
        have hK2 : 0 ≤ T uK 2 := (hcone_K (-1) (-1) (by norm_num) (by norm_num) uK
          (by dsimp [uK]; module)).2
        rw [(hscale uI ⟨2, -1, by dsimp [uI]; module⟩).2] at hI2
        rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).2] at hK2
        have hγ_le : γ ≤ 0 := nonpos_of_mul_nonpos_left hI2 h_no_vanish_I
        have hγ_ge : 0 ≤ γ := nonneg_of_mul_nonneg_left hK2 hK_pos
        exact hγ_ne (le_antisymm hγ_le hγ_ge)
    omega
  have hW_ne_top : W ≠ ⊤ := by
    intro htop
    have h3 : Module.finrank ℝ W =
        Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) := by rw [htop]
    rw [hW_finrank, finrank_top, finrank_euclideanSpace_fin] at h3
    norm_num at h3
  have hW_orth_ne_bot : Wᗮ ≠ ⊥ := by
    rwa [Ne, Submodule.orthogonal_eq_bot_iff]
  obtain ⟨b, hb_mem, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_orth_ne_bot
  have hb_w1 : ⟪b, T w₁⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hb_mem (T w₁) (Submodule.subset_span (by simp))
  have hb_w2 : ⟪b, T w₂⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hb_mem (T w₂) (Submodule.subset_span (by simp))
  have hW_orth_eq : (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ = W := by
    have hle : W ≤ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
      rw [← Submodule.orthogonal_orthogonal W]
      exact Submodule.orthogonal_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hb_mem))
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))
    rw [finrank_span_singleton hb_ne, finrank_euclideanSpace_fin] at hsum
    omega
  have h_beta_zero : ∀ x_c : Ambient d,
      (∀ m ∈ M₀, ⟪a m, x_c⟫_ℝ < 0) → ⟪b, T x_c⟫_ℝ = 0 := fun x_c hx_c => by
    refine hyperplane_miss_orthants_eq_zero hb_ne ⟪b, T x_c⟫_ℝ ?_ ?_
    · intro z hz_pos hdot
      have hz_diff : z - T x_c ∈ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_sub_left, real_inner_comm b z, real_inner_comm b (T x_c), hdot, sub_self]
      rw [hW_orth_eq, Submodule.mem_span_pair] at hz_diff
      obtain ⟨lam1, lam2, hcomb⟩ := hz_diff
      let x := x_c + lam1 • w₁ + lam2 • w₂
      have hTx : T x = z := by
        have h1 : T x = T x_c + (lam1 • T w₁ + lam2 • T w₂) := by
          dsimp [x]
          rw [map_add, map_add, map_smul, map_smul]; abel
        rw [h1, hcomb]; abel
      have hx_m : ∀ m ∈ M₀, ⟪a m, x⟫_ℝ < 0 := fun m hm => by
        have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        dsimp [x]
        rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        simpa using hx_c m hm
      have hx_ne0 : x ≠ 0 := by
        have hexm : M₀.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨m, hm⟩ := hexm
        intro hx0
        have := hx_m m hm
        rw [hx0, inner_zero_right] at this
        exact lt_irrefl 0 this
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne0
      let u_x : Ambient d := ‖x‖⁻¹ • x
      have hu_ball : u_x ∈ unitBall d := by
        change dist (‖x‖⁻¹ • x) 0 ≤ 1
        rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx_norm_pos.le),
          inv_mul_cancel₀ hx_norm_pos.ne']
      rw [hcov] at hu_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu_ball
      have hl_not_M : l ∉ M₀ := fun hlM => by
        have hge := hinner_a_ge l hl
        have hlt := hx_m l hlM
        dsimp [u_x] at hge
        rw [real_inner_smul_right] at hge
        have hge' := nonneg_of_mul_nonneg_right hge (inv_pos.mpr hx_norm_pos)
        linarith
      have hl_ijk : l = i ∨ l = j ∨ l = k := by
        by_contra hnone
        push Not at hnone
        exact hl_not_M (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hnone⟩)
      have hz0 : 0 < ⟪n i j, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 0
      have hz1 : 0 < ⟪n j k, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 1
      have hz2 : 0 < ⟪n k i, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 2
      rcases hl_ijk with hli | hlj | hlk
      · rw [hli] at hl
        have hle := (hsep_all i (hS_univ ▸ Finset.mem_univ i) k
          (hS_univ ▸ Finset.mem_univ k) hik).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym k i, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlj] at hl
        have hle := (hsep_all j (hS_univ ▸ Finset.mem_univ j) i
          (hS_univ ▸ Finset.mem_univ i) hij.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym i j, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlk] at hl
        have hle := (hsep_all k (hS_univ ▸ Finset.mem_univ k) j
          (hS_univ ▸ Finset.mem_univ j) hjk.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym j k, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
    · intro z hz_neg hdot
      have hz_diff : z - T x_c ∈ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_sub_left, real_inner_comm b z, real_inner_comm b (T x_c), hdot, sub_self]
      rw [hW_orth_eq, Submodule.mem_span_pair] at hz_diff
      obtain ⟨lam1, lam2, hcomb⟩ := hz_diff
      let x := x_c + lam1 • w₁ + lam2 • w₂
      have hTx : T x = z := by
        have h1 : T x = T x_c + (lam1 • T w₁ + lam2 • T w₂) := by
          dsimp [x]; rw [map_add, map_add, map_smul, map_smul]; abel
        rw [h1, hcomb]; abel
      have hx_m : ∀ m ∈ M₀, ⟪a m, x⟫_ℝ < 0 := fun m hm => by
        have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        dsimp [x]
        rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        simpa using hx_c m hm
      have hx_ne0 : x ≠ 0 := by
        have hexm : M₀.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨m, hm⟩ := hexm
        intro hx0
        have := hx_m m hm
        rw [hx0, inner_zero_right] at this
        exact lt_irrefl 0 this
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne0
      let u_x : Ambient d := ‖x‖⁻¹ • x
      have hu_ball : u_x ∈ unitBall d := by
        change dist (‖x‖⁻¹ • x) 0 ≤ 1
        rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx_norm_pos.le),
          inv_mul_cancel₀ hx_norm_pos.ne']
      rw [hcov] at hu_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu_ball
      have hl_not_M : l ∉ M₀ := fun hlM => by
        have hge := hinner_a_ge l hl
        have hlt := hx_m l hlM
        dsimp [u_x] at hge
        rw [real_inner_smul_right] at hge
        have hge' := nonneg_of_mul_nonneg_right hge (inv_pos.mpr hx_norm_pos)
        linarith
      have hl_ijk : l = i ∨ l = j ∨ l = k := by
        by_contra hnone
        push Not at hnone
        exact hl_not_M (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hnone⟩)
      have hz0 : ⟪n i j, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 0
      have hz1 : ⟪n j k, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 1
      have hz2 : ⟪n k i, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 2
      rcases hl_ijk with hli | hlj | hlk
      · rw [hli] at hl
        have hle := (hsep_all i (hS_univ ▸ Finset.mem_univ i) j
          (hS_univ ▸ Finset.mem_univ j) hij).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlj] at hl
        have hle := (hsep_all j (hS_univ ▸ Finset.mem_univ j) k
          (hS_univ ▸ Finset.mem_univ k) hjk).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlk] at hl
        have hle := (hsep_all k (hS_univ ▸ Finset.mem_univ k) i
          (hS_univ ▸ Finset.mem_univ i) hik.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
  have hbx0 : ⟪b, T x₀⟫_ℝ = 0 := h_beta_zero x₀ fun m hm => by
    have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
      simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hx₀_l m hm_not]; norm_num
  have hbe : ∀ m : Fin 6, ∀ hm : m ∈ M₀, ⟪b, T (eOf m hm)⟫_ℝ = 0 := fun m hm => by
    have hxm : ∀ l ∈ M₀, ⟪a l, x₀ + eOf m hm⟫_ℝ < 0 := fun l hl => by
      have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by
        simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have hli : l ≠ i := (Finset.mem_filter.mp hl).2.1
      rw [inner_add_right, hx₀_l l hl_not, heOf m hm l]
      split_ifs <;> norm_num
    have hsum0 := h_beta_zero (x₀ + eOf m hm) hxm
    rw [map_add, inner_add_right, hbx0, zero_add] at hsum0
    exact hsum0
  let v : Ambient d := b 0 • n i j + b 1 • n j k + b 2 • n k i
  have hv_inner : ∀ x : Ambient d, ⟪v, x⟫_ℝ = ⟪b, T x⟫_ℝ := fun x => by
    conv_rhs => rw [PiLp.inner_apply, Fin.sum_univ_three]
    dsimp [v, T]
    simp only [inner_add_left, real_inner_smul_left, real_inner_eq_re_inner,
      RCLike.inner_apply, conj_trivial]
    change b 0 * ⟪n i j, x⟫_ℝ + b 1 * ⟪n j k, x⟫_ℝ + b 2 * ⟪n k i, x⟫_ℝ =
      T x 0 * b 0 + T x 1 * b 1 + T x 2 * b 2
    have ht0 : T x 0 = ⟪n i j, x⟫_ℝ := rfl
    have ht1 : T x 1 = ⟪n j k, x⟫_ℝ := rfl
    have ht2 : T x 2 = ⟪n k i, x⟫_ℝ := rfl
    rw [ht0, ht1, ht2]
    ring
  have hv0 : v = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    let x := v
    let basisSum : Ambient d :=
      (∑ m ∈ M₀, (-⟪a m, x⟫_ℝ) • (if hm : m ∈ M₀ then eOf m hm - w₁ else 0)) +
        ⟪a i, x⟫_ℝ • w₁ + ⟪a j, x⟫_ℝ • w₂
    let y : Ambient d := x - basisSum
    have hy_m : ∀ m ∈ M₀, ⟪a m, y⟫_ℝ = 0 := fun m hm => by
      have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
        simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have hmi : m ≠ i := (Finset.mem_filter.mp hm).2.1
      have hbasis : ⟪a m, basisSum⟫_ℝ = ⟪a m, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a m, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = ⟪a m, x⟫_ℝ := by
          rw [Finset.sum_eq_single m]
          · simp only [hm, ↓reduceDIte, real_inner_smul_right, inner_sub_right,
              heOf m hm m, ↓reduceIte, (hw_m m hm_not).1]
            ring
          · intro m' hm' hm'm
            simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
              heOf m' hm' m, hm'm.symm, hmi, ↓reduceIte, (hw_m m hm_not).1]
            ring
          · intro hm'; exact False.elim (hm' hm)
        rw [hsum, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        ring
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_i : ⟪a i, y⟫_ℝ = 0 := by
      have hbasis : ⟪a i, basisSum⟫_ℝ = ⟪a i, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a i, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = 0 := by
          refine Finset.sum_eq_zero fun m' hm' => ?_
          have hm'i : i ≠ m' := ((Finset.mem_filter.mp hm').2.1).symm
          simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
            heOf m' hm' i, hm'i, ↓reduceIte, hw₁ i]
          ring
        rw [hsum, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
        simp [hij, hik]
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_j : ⟪a j, y⟫_ℝ = 0 := by
      have hbasis : ⟪a j, basisSum⟫_ℝ = ⟪a j, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a j, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = 0 := by
          refine Finset.sum_eq_zero fun m' hm' => ?_
          have hm'j : j ≠ m' := ((Finset.mem_filter.mp hm').2.2.1).symm
          simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
            heOf m' hm' j, hm'j, ↓reduceIte, hw₁ j, hij.symm, hjk]
          ring
        rw [hsum, real_inner_smul_right, real_inner_smul_right, hw₁ j, hw₂ j]
        simp [hij.symm, hjk]
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_k : ⟪a k, y⟫_ℝ = 0 := by
      have htot : ∑ l : Fin 6, ⟪a l, y⟫_ℝ = 0 := by
        rw [← sum_inner, ha_sum0, inner_zero_left]
      have hsplit : ∑ l ∈ Finset.univ.erase k, ⟪a l, y⟫_ℝ = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        by_cases hli : l = i
        · exact hli ▸ hy_i
        · by_cases hlj : l = j
          · exact hlj ▸ hy_j
          · exact hy_m l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli, hlj, hlk⟩)
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), hsplit, add_zero] at htot
      exact htot
    have hy_all : ∀ l : Fin 6, ⟪a l, y⟫_ℝ = 0 := fun l => by
      by_cases hli : l = i
      · exact hli ▸ hy_i
      · by_cases hlj : l = j
        · exact hlj ▸ hy_j
        · by_cases hlk : l = k
          · exact hlk ▸ hy_k
          · exact hy_m l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli, hlj, hlk⟩)
    have hy_n : ∀ p q : Fin 6, ⟪n p q, y⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS
        (fun p hp q hq hpq => ⟨(hsep_all p hp q hq hpq).1, (hsep_all p hp q hq hpq).2.1⟩)
        hnsym hy_all
    have hvy : ⟪v, y⟫_ℝ = 0 := by
      dsimp [v]
      simp only [inner_add_left, real_inner_smul_left, hy_n i j, hy_n j k, hy_n k i,
        mul_zero, add_zero]
    have hvb : ⟪v, basisSum⟫_ℝ = 0 := by
      dsimp [basisSum]
      rw [inner_add_right, inner_add_right, inner_sum]
      have hsum : (∑ m ∈ M₀, ⟪v, (-⟪a m, x⟫_ℝ) •
          (if hm : m ∈ M₀ then eOf m hm - w₁ else 0)⟫_ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [dif_pos hm, real_inner_smul_right]
        have h1 : ⟪v, eOf m hm - w₁⟫_ℝ = 0 := by
          rw [inner_sub_right, hv_inner, hbe m hm, hv_inner, hb_w1, sub_zero]
        rw [h1, mul_zero]
      rw [hsum, real_inner_smul_right, real_inner_smul_right, hv_inner, hb_w1,
        hv_inner, hb_w2]
      ring
    have hvx : ⟪v, x⟫_ℝ = ⟪v, y⟫_ℝ + ⟪v, basisSum⟫_ℝ := by
      dsimp [y]
      rw [inner_sub_right]
      ring
    rw [hvy, hvb, add_zero] at hvx
    exact hvx
  have hb_nz : b 0 ≠ 0 ∨ b 1 ≠ 0 ∨ b 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hb_ne
    ext r
    fin_cases r <;> simp [hall]
  exact ⟨b 0, b 1, b 2, hb_nz, hv0⟩

private lemma finrank_triangle_span_le {d n : ℕ} (v : Fin n → Fin n → Ambient d)
    (hanti : ∀ i j, v j i = - v i j) (hne : ∀ i j, i ≠ j → v i j ≠ 0)
    (htri : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ∃ c₁ c₂ c₃ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
        c₁ • v i j + c₂ • v j k + c₃ • v k i = 0) :
    ∀ k : ℕ, ∀ A : Finset (Fin n), A.Nonempty → A.card = k →
      Module.finrank ℝ (Submodule.span ℝ {x | ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ x = v i j}) ≤ k - 1 := by
  intro k
  induction k with
  | zero =>
    intro A hAne hcard
    exfalso
    exact hAne.ne_empty (Finset.card_eq_zero.mp hcard)
  | succ k ih =>
    intro A hAne hcard
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      subst hx
      have hset : {y | ∃ i ∈ ({x} : Finset (Fin n)), ∃ j ∈ ({x} : Finset (Fin n)),
          i ≠ j ∧ y = v i j} = ∅ := by
        ext y
        simp only [Finset.mem_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, rfl, j, rfl, hij, _⟩
        exact hij rfl
      rw [hset, Submodule.span_empty, finrank_bot]
    · obtain ⟨x, hxA⟩ := hAne
      let B := A.erase x
      have hB_card : B.card = k := by
        rw [Finset.card_erase_of_mem hxA, hcard]; simp
      have hB_ne : B.Nonempty := Finset.card_pos.mp (by omega)
      have hih := ih B hB_ne hB_card
      let W_A := Submodule.span ℝ {y | ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ y = v i j}
      let W_B := Submodule.span ℝ {y | ∃ i ∈ B, ∃ j ∈ B, i ≠ j ∧ y = v i j}
      have hex_w0 : ∃ w₀ : Ambient d, W_A ≤ W_B ⊔ Submodule.span ℝ {w₀} := by
        by_cases hall : ∀ b ∈ B, v x b ∈ W_B
        · refine ⟨0, Submodule.span_le.mpr ?_⟩
          rintro y ⟨i, hiA, j, hjA, hij, rfl⟩
          rw [SetLike.mem_coe]
          by_cases hix : i = x
          · subst hix
            have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hij.symm, hjA⟩
            exact Submodule.mem_sup_left (hall j hjB)
          · by_cases hjx : j = x
            · subst hjx
              have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hij, hiA⟩
              rw [hanti j i]
              exact Submodule.neg_mem _ (Submodule.mem_sup_left (hall i hiB))
            · have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hix, hiA⟩
              have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hjx, hjA⟩
              exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, hiB, j, hjB, hij, rfl⟩)
        · push Not at hall
          obtain ⟨b₀, hb₀B, hb₀_not⟩ := hall
          have hb₀_ne_x : b₀ ≠ x := (Finset.mem_erase.mp hb₀B).1
          refine ⟨v x b₀, Submodule.span_le.mpr ?_⟩
          have hxb : ∀ b ∈ B, v x b ∈ W_B ⊔ Submodule.span ℝ {v x b₀} := fun b hbB => by
            by_cases hbb0 : b = b₀
            · subst hbb0
              exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
            · have hbx_ne : b ≠ x := (Finset.mem_erase.mp hbB).1
              obtain ⟨c₁, c₂, c₃, hcnz, hceq⟩ := htri x b₀ b hb₀_ne_x.symm (Ne.symm hbb0) hbx_ne.symm
              have hc₃_ne : c₃ ≠ 0 := by
                intro hc₃
                rw [hc₃, zero_smul, add_zero] at hceq
                have hc₁_ne : c₁ ≠ 0 := by
                  intro hc₁
                  rw [hc₁, zero_smul, zero_add, smul_eq_zero] at hceq
                  rcases hceq with hc₂ | hv0
                  · exact hcnz.elim (absurd hc₁) (fun h => h.elim (absurd hc₂) (absurd hc₃))
                  · exact hne b₀ b (Ne.symm hbb0) hv0
                have hv_eq : v x b₀ = (-c₂ / c₁) • v b₀ b := by
                  have h1 := congrArg (c₁⁻¹ • ·) hceq
                  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc₁_ne, one_smul,
                    smul_zero] at h1
                  have h2 := eq_neg_of_add_eq_zero_left h1
                  rw [h2, ← neg_smul]
                  congr 1; ring
                apply hb₀_not
                rw [hv_eq]
                exact Submodule.smul_mem _ _
                  (Submodule.subset_span ⟨b₀, hb₀B, b, hbB, Ne.symm hbb0, rfl⟩)
              have hv_eq : v x b = (c₁ / c₃) • v x b₀ + (c₂ / c₃) • v b₀ b := by
                rw [hanti x b, smul_neg] at hceq
                have hsub : c₁ • v x b₀ + c₂ • v b₀ b = c₃ • v x b :=
                  eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hceq)
                have h1 := congrArg (c₃⁻¹ • ·) hsub
                rw [smul_add, smul_smul, smul_smul, smul_smul,
                  inv_mul_cancel₀ hc₃_ne, one_smul] at h1
                rw [← h1]
                congr 1 <;> congr 1 <;> ring
              rw [hv_eq]
              refine Submodule.add_mem _ ?_ ?_
              · exact Submodule.mem_sup_right
                  (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
              · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
                  (Submodule.subset_span ⟨b₀, hb₀B, b, hbB, Ne.symm hbb0, rfl⟩))
          rintro y ⟨i, hiA, j, hjA, hij, rfl⟩
          rw [SetLike.mem_coe]
          by_cases hix : i = x
          · subst hix
            exact hxb j (Finset.mem_erase.mpr ⟨hij.symm, hjA⟩)
          · by_cases hjx : j = x
            · rw [hjx, hanti x i]
              exact Submodule.neg_mem _ (hxb i (Finset.mem_erase.mpr ⟨hix, hiA⟩))
            · have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hix, hiA⟩
              have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hjx, hjA⟩
              exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, hiB, j, hjB, hij, rfl⟩)
      obtain ⟨w₀, hw₀⟩ := hex_w0
      have hfin_le : Module.finrank ℝ W_A ≤
          Module.finrank ℝ W_B + Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) :=
        (Submodule.finrank_mono hw₀).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
      have hspan_w0 : Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) ≤ 1 := by
        have h1 : Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) ≤
            ({w₀} : Set (Ambient d)).toFinset.card :=
          finrank_span_le_card ({w₀} : Set (Ambient d))
        have h2 : ({w₀} : Set (Ambient d)).toFinset.card ≤ 1 := by simp
        exact h1.trans h2
      change Module.finrank ℝ W_B ≤ k - 1 at hih
      change Module.finrank ℝ W_A ≤ (k + 1) - 1
      omega

private lemma fin_succ_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) : a.succ ≠ b.succ :=
  fun heq => h (Fin.ext (Nat.succ.inj (congrArg Fin.val heq)))

private def castPair {n m : ℕ} (h : n = m) (e : Pairs n) : Pairs m :=
  ⟨(Fin.cast h e.1.1, Fin.cast h e.1.2), e.2⟩

private lemma castPair_rfl {n : ℕ} (e : Pairs n) : castPair rfl e = e :=
  Subtype.ext (Prod.ext rfl rfl)

private inductive TreeShape (d : ℕ) : ℕ → Type
  | unit : TreeShape d 0
  | star (q : Fin 6)
      (perm : Equiv.Perm (Fin (q.1 + 1)))
      (I : {I : Fin q.1 → Fin d // Function.Injective I})
      (k₀ : Fin q.1 → Fin q.1)
      (root : Fin q.1 → Fin q.1)
      (useLeft : Pairs q.1 → Bool) : TreeShape d 0
  | lift {fuel : ℕ} (sh : TreeShape d fuel) : TreeShape d (fuel + 1)
  | split {fuel : ℕ} (q s : Fin 6)
      (cls : Fin q.1 → Fin s.1)
      (shU : TreeShape d fuel)
      (shC : Fin s.1 → TreeShape d fuel) : TreeShape d (fuel + 1)

private instance instFiniteTreeShape (d fuel : ℕ) : Finite (TreeShape d fuel) := by
  induction fuel with
  | zero =>
    let T0 := Option (Σ q : Fin 6, Equiv.Perm (Fin (q.1 + 1)) ×
      {I : Fin q.1 → Fin d // Function.Injective I} ×
      (Fin q.1 → Fin q.1) × (Fin q.1 → Fin q.1) × (Pairs q.1 → Bool))
    let f : TreeShape d 0 → T0
      | .unit => none
      | .star q perm I k₀ root useLeft => some ⟨q, perm, I, k₀, root, useLeft⟩
    let g : T0 → TreeShape d 0
      | none => .unit
      | some ⟨q, perm, I, k₀, root, useLeft⟩ => .star q perm I k₀ root useLeft
    have hli : Function.LeftInverse g f := fun x => by cases x <;> rfl
    exact Finite.of_injective f hli.injective
  | succ fuel ih =>
    let T1 := TreeShape d fuel ⊕ (Σ q : Fin 6, Σ s : Fin 6,
      (Fin q.1 → Fin s.1) × TreeShape d fuel × (Fin s.1 → TreeShape d fuel))
    let f : TreeShape d (fuel + 1) → T1
      | .lift sh => Sum.inl sh
      | .split q s cls shU shC => Sum.inr ⟨q, s, cls, shU, shC⟩
    let g : T1 → TreeShape d (fuel + 1)
      | Sum.inl sh => .lift sh
      | Sum.inr ⟨q, s, cls, shU, shC⟩ => .split q s cls shU shC
    have hli : Function.LeftInverse g f := fun x => by cases x <;> rfl
    exact Finite.of_injective f hli.injective

private def TreeShape.dim {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → ℕ
  | 0, .unit => 0
  | 0, .star q _ _ _ _ _ => q.1
  | _ + 1, .lift sh => sh.dim
  | _ + 1, .split q _ _ _ _ => q.1

private def classSet (q s : ℕ) (cls : Fin q → Fin s) (r : Fin s) : Finset (Fin q) :=
  Finset.univ.filter fun a => cls a = r

private def TreeShape.Valid {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → Prop
  | 0, .unit => True
  | 0, .star q _ _ _ root _ => 1 ≤ q.1 ∧ q.1 ≤ d ∧ ∃ a₀ : Fin q.1, root a₀ = a₀
  | _ + 1, .lift sh => sh.Valid
  | _ + 1, .split q s cls shU shC =>
      2 ≤ q.1 ∧ q.1 ≤ d ∧ 1 ≤ s.1 ∧ s.1 < q.1 ∧
      (∀ r : Fin s.1, 1 ≤ (classSet q.1 s.1 cls r).card) ∧
      shU.Valid ∧ shU.dim = s.1 ∧
      ∀ r : Fin s.1, (shC r).Valid ∧ (shC r).dim = (classSet q.1 s.1 cls r).card - 1

private def TreeShape.ParamIdx {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → Type
  | 0, .unit => Empty
  | 0, .star q _ I k₀ root _ =>
      (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
      (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
      {a : Fin q.1 // root a ≠ a}
  | _ + 1, .lift sh => sh.ParamIdx
  | _ + 1, .split _ s _ shU shC =>
      shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx)

private noncomputable instance TreeShape.fintypeParamIdx {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) → Fintype sh.ParamIdx
  | 0, .unit => by
      change Fintype Empty
      exact inferInstance
  | 0, .star q _ I k₀ root _ => by
      change Fintype (
        (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
        (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
        {a : Fin q.1 // root a ≠ a})
      classical
      exact inferInstance
  | _ + 1, .lift sh => sh.fintypeParamIdx
  | _ + 1, .split _ s _ shU shC => by
      change Fintype (shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx))
      letI := shU.fintypeParamIdx
      letI := fun r => (shC r).fintypeParamIdx
      exact inferInstance

private lemma TreeShape.dim_le_d {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) → sh.Valid → sh.dim ≤ d
  | 0, .unit, _ => Nat.zero_le d
  | 0, .star _ _ _ _ _ _, h => h.2.1
  | _ + 1, .lift sh, h => sh.dim_le_d h
  | _ + 1, .split _ _ _ _ _, h => h.2.1

private lemma card_paramIdx_bound {d fuel : ℕ} (sh : TreeShape d fuel) (hv : sh.Valid) :
    Fintype.card sh.ParamIdx ≤ sh.dim * d - 1 := by
  induction fuel generalizing d with
  | zero =>
    cases sh with
    | unit =>
      haveI : IsEmpty (TreeShape.unit (d := d)).ParamIdx := by
        change IsEmpty Empty
        exact inferInstance
      rw [Fintype.card_eq_zero]
      exact Nat.zero_le _
    | star q perm I k₀ root useLeft =>
      rcases hv with ⟨hq1, hqd, a₀, ha₀⟩
      have hcard_eq : Fintype.card (TreeShape.star q perm I k₀ root useLeft).ParamIdx = by
          classical
          exact Fintype.card (
            (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
            (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
            {a : Fin q.1 // root a ≠ a}) := by
        classical
        exact Fintype.card_congr (Equiv.refl _)
      rw [hcard_eq]
      change _ ≤ q.1 * d - 1
      have hcard_free : Fintype.card {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j} = d - q.1 := by
        let p : Fin d → Prop := fun j => ∃ s : Fin q.1, I.1 s = j
        have heq1 : Fintype.card {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j} =
            Fintype.card {j : Fin d // ¬ p j} := by
          refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
          simp only [p]
          push Not
          rfl
        have heq2 : Fintype.card {j : Fin d // ¬ p j} = d - Fintype.card {j : Fin d // p j} := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin]
        have heq3 : Fintype.card {j : Fin d // p j} = q.1 := by
          let f : Fin q.1 → {j : Fin d // p j} := fun s => ⟨I.1 s, s, rfl⟩
          have hf_bij : Function.Bijective f := by
            refine ⟨fun s₁ s₂ h => I.2 (congrArg Subtype.val h), fun ⟨j, s, hs⟩ => ?_⟩
            exact ⟨s, Subtype.ext hs⟩
          exact (Fintype.card_of_bijective hf_bij).symm.trans (Fintype.card_fin q.1)
        rw [heq1, heq2, heq3]
      have hcard_k₀ : ∀ a : Fin q.1, Fintype.card {r : Fin q.1 // r ≠ k₀ a} = q.1 - 1 := fun a => by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
      have hcard_root : Fintype.card {a : Fin q.1 // root a ≠ a} ≤ q.1 - 1 := by
        let g : {a : Fin q.1 // root a ≠ a} → {a : Fin q.1 // a ≠ a₀} := fun ⟨a, ha⟩ =>
          ⟨a, fun h => ha (h ▸ ha₀)⟩
        have hg : Function.Injective g := by
          rintro ⟨a, ha⟩ ⟨b, hb⟩ h
          have hab : a = b := congrArg Subtype.val h
          exact Subtype.ext hab
        have hle := Fintype.card_le_of_injective g hg
        have heq : Fintype.card {a : Fin q.1 // a ≠ a₀} = q.1 - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
        omega
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        hcard_free, Fintype.card_sigma]
      simp only [hcard_k₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hcalc1 : q.1 * (d - q.1) + q.1 * (q.1 - 1) = q.1 * (d - 1) := by
        rw [← mul_add, show d - q.1 + (q.1 - 1) = d - 1 by omega]
      have hcalc3 : q.1 * (d - 1) + (q.1 - 1) = q.1 * d - 1 := by
        rw [Nat.mul_sub_left_distrib, mul_one]
        have hqd1 : q.1 ≤ q.1 * d := Nat.le_mul_of_pos_right q.1 (by omega)
        omega
      omega
  | succ fuel ih =>
    cases sh with
    | lift sh => exact ih sh hv
    | split q s cls shU shC =>
      rcases hv with ⟨hq2, hqd, hs1, hsq, hcard_ge, hUval, hUdim, hCval⟩
      have hcard_eq : Fintype.card (TreeShape.split q s cls shU shC).ParamIdx =
          @Fintype.card (shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx)) (by
            letI := shU.fintypeParamIdx
            letI := fun r => (shC r).fintypeParamIdx
            exact inferInstance) :=
        Fintype.card_congr (Equiv.refl _)
      rw [hcard_eq]
      letI := shU.fintypeParamIdx
      letI := fun r => (shC r).fintypeParamIdx
      rw [Fintype.card_sum, Fintype.card_sigma]
      change _ + _ ≤ q.1 * d - 1
      have hU_le : Fintype.card shU.ParamIdx ≤ s.1 * d - 1 := by
        have h := ih shU hUval
        rwa [hUdim] at h
      have hC_le : ∀ r : Fin s.1,
          Fintype.card (shC r).ParamIdx ≤ ((classSet q.1 s.1 cls r).card - 1) * d := fun r => by
        have h := ih (shC r) (hCval r).1
        rw [(hCval r).2] at h
        exact h.trans (Nat.sub_le _ _)
      have hsum_C : (∑ r : Fin s.1, Fintype.card (shC r).ParamIdx) ≤
          (∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1)) * d := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun r _ => hC_le r
      have hfib : ∑ r : Fin s.1, (classSet q.1 s.1 cls r).card = q.1 := by
        have h := Finset.card_eq_sum_card_fiberwise (f := cls) (s := Finset.univ) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (cls a))
        simpa [classSet] using h.symm
      have hsum_sub : s.1 + ∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1) = q.1 := by
        have h1 : ∑ r : Fin s.1, (classSet q.1 s.1 cls r).card =
            ∑ r : Fin s.1, (1 + ((classSet q.1 s.1 cls r).card - 1)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hcr := hcard_ge r
          omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one] at hfib
        exact hfib
      have h1d : 1 ≤ d := by omega
      have hsd : 1 ≤ s.1 * d := Nat.mul_pos hs1 h1d
      have hmul : s.1 * d + (∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1)) * d = q.1 * d := by
        rw [← add_mul, hsum_sub]
      omega

private noncomputable def evalStar {d : ℕ} (q : Fin 6)
    (perm : Equiv.Perm (Fin (q.1 + 1)))
    (I : {I : Fin q.1 → Fin d // Function.Injective I})
    (k₀ root : Fin q.1 → Fin q.1)
    (useLeft : Pairs q.1 → Bool)
    (θ : (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
         (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
         {a : Fin q.1 // root a ≠ a} → ℝ)
    (e : Pairs (q.1 + 1)) : Ambient d :=
  let u : Fin q.1 → Ambient d := fun r =>
    ∑ j : Fin d,
      (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
        θ (Sum.inl (r, ⟨j, hj⟩))
      else
        if I.1 r = j then (1 : ℝ) else 0) •
      EuclideanSpace.single j (1 : ℝ)
  let w : Fin q.1 → Ambient d := fun a =>
    ∑ r : Fin q.1,
      (if hr : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) • u r
  let t : Fin q.1 → ℝ := fun a =>
    if ha : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha⟩))
  let i := perm.symm e.1.1
  let j := perm.symm e.1.2
  Fin.cases
    (Fin.cases (0 : Ambient d) (fun b => w b) j)
    (fun a => Fin.cases (-w a) (fun b =>
      if root a = root b then t a • w a - t b • w b
      else if hab : a < b then if useLeft ⟨(a, b), hab⟩ then w a else w b
      else if hba : b < a then if useLeft ⟨(b, a), hba⟩ then w b else w a
      else 0) j)
    i

private lemma differentiable_ite {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Prop} [Decidable P] {f g : E → F}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun x => if P then f x else g x) := by
  by_cases h : P <;> simp [h, hf, hg]

private lemma differentiable_dite {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Prop} [Decidable P]
    {f : P → E → F} {g : ¬ P → E → F}
    (hf : ∀ h : P, Differentiable ℝ (f h)) (hg : ∀ h : ¬ P, Differentiable ℝ (g h)) :
    Differentiable ℝ (fun x => if h : P then f h x else g h x) := by
  by_cases h : P
  · simpa [h] using hf h
  · simpa [h] using hg h

private lemma differentiable_fin_cases {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : Fin (n + 1)) {f0 : E → F} {fs : Fin n → E → F}
    (hf0 : Differentiable ℝ f0) (hfs : ∀ i, Differentiable ℝ (fs i)) :
    Differentiable ℝ (fun x => Fin.cases (motive := fun _ => F) (f0 x) (fun i => fs i x) k) := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · exact hf0
  · exact hfs i

private lemma differentiable_evalStar {d : ℕ} (q : Fin 6)
    (perm : Equiv.Perm (Fin (q.1 + 1)))
    (I : {I : Fin q.1 → Fin d // Function.Injective I})
    (k₀ root : Fin q.1 → Fin q.1)
    (useLeft : Pairs q.1 → Bool)
    (e : Pairs (q.1 + 1)) :
    Differentiable ℝ (fun θ => evalStar q perm I k₀ root useLeft θ e) := by
  let γ := (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
    (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕ {a : Fin q.1 // root a ≠ a}
  have hu : ∀ r : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      ∑ j : Fin d,
        (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
          θ (Sum.inl (r, ⟨j, hj⟩))
        else if I.1 r = j then (1 : ℝ) else 0) •
        EuclideanSpace.single j (1 : ℝ)) := fun r => by
    refine Differentiable.fun_sum fun j _ => ?_
    by_cases hj : ∀ s : Fin q.1, I.1 s ≠ j
    · have hfn : (fun θ : γ → ℝ =>
          (if hj' : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj'⟩))
           else if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ)) =
          fun θ => θ (Sum.inl (r, ⟨j, hj⟩)) • EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_apply _).smul_const _
    · have hfn : (fun θ : γ → ℝ =>
          (if hj' : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj'⟩))
           else if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ)) =
          fun _ => (if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact differentiable_const _
  have hw : ∀ a : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      ∑ r : Fin q.1,
        (if hr : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) •
        (∑ j : Fin d,
          (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
            θ (Sum.inl (r, ⟨j, hj⟩))
          else if I.1 r = j then (1 : ℝ) else 0) •
          EuclideanSpace.single j (1 : ℝ))) := fun a => by
    refine Differentiable.fun_sum fun r _ => ?_
    by_cases hr : r = k₀ a
    · have hfn : (fun θ : γ → ℝ =>
          (if hr' : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr'⟩⟩))) •
          ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = fun θ =>
          (1 : ℝ) • ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_const (1 : ℝ)).smul (hu r)
    · have hfn : (fun θ : γ → ℝ =>
          (if hr' : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr'⟩⟩))) •
          ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = fun θ =>
          θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩)) • ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_apply _).smul (hu r)
  have ht : ∀ a : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      if ha : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha⟩))) := fun a => by
    by_cases ha : root a = a
    · have hfn : (fun θ : γ → ℝ =>
          if ha' : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha'⟩))) = fun _ => 1 :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]; exact differentiable_const _
    · have hfn : (fun θ : γ → ℝ =>
          if ha' : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha'⟩))) =
          fun θ => θ (Sum.inr (Sum.inr ⟨a, ha⟩)) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]; exact differentiable_apply _
  unfold evalStar
  refine differentiable_fin_cases (perm.symm e.1.1) ?_ fun a => ?_
  · refine differentiable_fin_cases (perm.symm e.1.2) (differentiable_const 0) fun b => hw b
  · refine differentiable_fin_cases (perm.symm e.1.2) (hw a).neg fun b => ?_
    refine differentiable_ite (((ht a).smul (hw a)).sub ((ht b).smul (hw b))) ?_
    refine differentiable_dite (fun hab => ?_) (fun _ => ?_)
    · exact differentiable_ite (hw a) (hw b)
    · refine differentiable_dite (fun hba => ?_) (fun _ => differentiable_const 0)
      exact differentiable_ite (hw b) (hw a)

private noncomputable def TreeShape.evalEdges {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) →
    (sh.ParamIdx → ℝ) → Pairs (sh.dim + 1) → Ambient d
  | 0, .unit, _, _ => 0
  | 0, .star q perm I k₀ root useLeft, θ, e => evalStar q perm I k₀ root useLeft θ e
  | _ + 1, .lift sh, θ, e => sh.evalEdges θ e
  | _ + 1, .split q s cls shU shC, θ, e =>
      Fin.cases
        (Fin.cases (0 : Ambient d) (fun b =>
          if hU : s.1 + 1 = shU.dim + 1 then
            shU.evalEdges (fun x => θ (Sum.inl x))
              (castPair hU ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
          else 0) e.1.2)
        (fun a => Fin.cases (0 : Ambient d) (fun b =>
          if hcls : cls a = cls b then
            let r := cls a
            let C := classSet q.1 s.1 cls r
            if hC : C.card = (shC r).dim + 1 then
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card :=
                ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              if hij' : i' < j' then
                (shC r).evalEdges (fun x => θ (Sum.inr ⟨r, x⟩))
                  (castPair hC ⟨(i', j'), hij'⟩)
              else 0
            else 0
          else
            if hU : s.1 + 1 = shU.dim + 1 then
              if hlt : cls a < cls b then
                shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
              else if hgt : cls b < cls a then
                - shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
              else 0
            else 0) e.1.2)
        e.1.1

private lemma evalEdges_split {d fuel : ℕ} (q s : Fin 6)
    (cls : Fin q.1 → Fin s.1) (shU : TreeShape d fuel) (shC : Fin s.1 → TreeShape d fuel)
    (θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ) (e : Pairs (q.1 + 1)) :
    (TreeShape.split q s cls shU shC).evalEdges θ e =
      Fin.cases
        (Fin.cases (0 : Ambient d) (fun b =>
          if hU : s.1 + 1 = shU.dim + 1 then
            shU.evalEdges (fun x => θ (Sum.inl x))
              (castPair hU ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
          else 0) e.1.2)
        (fun a => Fin.cases (0 : Ambient d) (fun b =>
          if hcls : cls a = cls b then
            let r := cls a
            let C := classSet q.1 s.1 cls r
            if hC : C.card = (shC r).dim + 1 then
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card :=
                ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              if hij' : i' < j' then
                (shC r).evalEdges (fun x => θ (Sum.inr ⟨r, x⟩))
                  (castPair hC ⟨(i', j'), hij'⟩)
              else 0
            else 0
          else
            if hU : s.1 + 1 = shU.dim + 1 then
              if hlt : cls a < cls b then
                shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
              else if hgt : cls b < cls a then
                - shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
              else 0
            else 0) e.1.2)
        e.1.1 := rfl

private lemma differentiable_evalEdges {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) →
    (e : Pairs (sh.dim + 1)) →
    Differentiable ℝ (fun θ : sh.ParamIdx → ℝ => sh.evalEdges θ e)
  | 0, .unit, _ => differentiable_const _
  | 0, .star q perm I k₀ root useLeft, e => differentiable_evalStar q perm I k₀ root useLeft e
  | _ + 1, .lift sh, e => differentiable_evalEdges sh e
  | _ + 1, .split q s cls shU shC, e => by
    unfold TreeShape.evalEdges
    have hinl : Differentiable ℝ (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
        fun x : shU.ParamIdx => θ (Sum.inl x)) :=
      differentiable_pi.mpr fun x => differentiable_apply (Sum.inl x)
    have hinr : ∀ r : Fin s.1, Differentiable ℝ
        (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
          fun x : (shC r).ParamIdx => θ (Sum.inr (Sigma.mk r x))) := fun r =>
      differentiable_pi.mpr fun x => by
        change Differentiable ℝ (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
          θ (Sum.inr (Sigma.mk r x)))
        exact differentiable_apply _
    refine differentiable_fin_cases e.1.1 ?_ fun a => ?_
    · refine differentiable_fin_cases e.1.2 (differentiable_const 0) fun b => ?_
      refine differentiable_dite (fun hU => (differentiable_evalEdges shU _).comp hinl)
        (fun _ => differentiable_const 0)
    · refine differentiable_fin_cases e.1.2 (differentiable_const 0) fun b => ?_
      refine differentiable_dite (fun hcls => ?_) (fun _ => ?_)
      · refine differentiable_dite (fun hC => ?_) (fun _ => differentiable_const 0)
        refine differentiable_dite (fun hij' => (differentiable_evalEdges (shC (cls a)) _).comp (hinr (cls a)))
          (fun _ => differentiable_const 0)
      · refine differentiable_dite (fun hU => ?_) (fun _ => differentiable_const 0)
        refine differentiable_dite (fun hlt => (differentiable_evalEdges shU _).comp hinl) (fun _ => ?_)
        exact differentiable_dite (fun hgt => ((differentiable_evalEdges shU _).comp hinl).neg)
          (fun _ => differentiable_const 0)

private lemma exists_liftShape {d : ℕ} {fuel₁ : ℕ} (fuel₂ : ℕ) (h : fuel₁ ≤ fuel₂)
    (sh : TreeShape d fuel₁) (hval : sh.Valid)
    (v : Pairs (sh.dim + 1) → Ambient d)
    (hrep : ∃ θ : sh.ParamIdx → ℝ, ∀ e : Pairs (sh.dim + 1),
      ∃ c : ℝ, c ≠ 0 ∧ sh.evalEdges θ e = c • v e) :
    ∃ (sh' : TreeShape d fuel₂) (heq : sh'.dim = sh.dim),
      sh'.Valid ∧
      ∃ θ' : sh'.ParamIdx → ℝ, ∀ e : Pairs (sh'.dim + 1),
        ∃ c : ℝ, c ≠ 0 ∧ sh'.evalEdges θ' e = c • v (castPair (congrArg (· + 1) heq) e) := by
  induction fuel₂ with
  | zero =>
    have h0 : fuel₁ = 0 := by omega
    subst h0
    refine ⟨sh, rfl, hval, ?_⟩
    obtain ⟨θ, hθ⟩ := hrep
    refine ⟨θ, fun e => ?_⟩
    rw [castPair_rfl]
    exact hθ e
  | succ f ih =>
    by_cases hle : fuel₁ ≤ f
    · obtain ⟨sh', heq, hval', θ', hθ'⟩ := ih hle
      exact ⟨.lift sh', heq, hval', θ', hθ'⟩
    · have hf : fuel₁ = f + 1 := by omega
      subst hf
      refine ⟨sh, rfl, hval, ?_⟩
      obtain ⟨θ, hθ⟩ := hrep
      refine ⟨θ, fun e => ?_⟩
      rw [castPair_rfl]
      exact hθ e

private lemma orderIsoOfFin_symm_val {α : Type*} [LinearOrder α] (S : Finset α)
    {n m : ℕ} (hn : S.card = n) (hm : S.card = m) (x : S) :
    ((S.orderIsoOfFin hn).symm x).1 = ((S.orderIsoOfFin hm).symm x).1 := by
  subst hn
  subst hm
  rfl

private lemma orderIsoOfFin_val_eq {α : Type*} [LinearOrder α] (S : Finset α)
    {n m : ℕ} (hn : S.card = n) (hm : S.card = m)
    (i : Fin n) (j : Fin m) (hij : (i : ℕ) = (j : ℕ)) :
    ((S.orderIsoOfFin hn) i).1 = ((S.orderIsoOfFin hm) j).1 := by
  subst hn
  subst hm
  have hij' : i = j := Fin.ext hij
  rw [hij']

private lemma exists_treeParam {d : ℕ} :
    ∀ (q : ℕ), 1 ≤ q → q ≤ 5 → q ≤ d →
      ∀ (v : Fin (q + 1) → Fin (q + 1) → Ambient d),
      (∀ i j, v j i = - v i j) →
      (∀ i j, i ≠ j → v i j ≠ 0) →
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • v i j + c₂ • v j k + c₃ • v k i = 0) →
      (q ≤ Module.finrank ℝ
        (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q + 1), x = v i j})) →
      ∃ (sh : TreeShape d q) (heq : sh.dim = q),
        sh.Valid ∧
        ∃ θ : sh.ParamIdx → ℝ,
          ∀ e : Pairs (sh.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
            sh.evalEdges θ e = c • v (Fin.cast (congrArg (· + 1) heq) e.1.1)
                                     (Fin.cast (congrArg (· + 1) heq) e.1.2) := by
  intro q
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq1 hq5 hqd v hv_sym hv_nz hv_tri hv_dim
    by_cases hstar : ∃ r₀ : Fin (q + 1),
        LinearIndependent ℝ (fun a : Fin q => v r₀ (r₀.succAbove a))
    · obtain ⟨r₀, hlin⟩ := hstar
      let q' : Fin 6 := ⟨q, by omega⟩
      let perm : Equiv.Perm (Fin (q'.1 + 1)) := Equiv.swap (0 : Fin (q + 1)) r₀
      let v' : Fin (q + 1) → Fin (q + 1) → Ambient d := fun i j => v (perm i) (perm j)
      have hv'_sym : ∀ i j, v' j i = - v' i j := fun i j => hv_sym (perm i) (perm j)
      have hv'_nz : ∀ i j, i ≠ j → v' i j ≠ 0 := fun i j hij =>
        hv_nz (perm i) (perm j) (fun h => hij (perm.injective h))
      have hv'_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧
            c₁ • v' i j + c₂ • v' j k + c₃ • v' k i = 0 := fun i j k hij hjk hik =>
        hv_tri (perm i) (perm j) (perm k) (fun h => hij (perm.injective h))
          (fun h => hjk (perm.injective h)) (fun h => hik (perm.injective h))
      let w : Fin q → Ambient d := fun a => v' 0 a.succ
      have hw_indep : LinearIndependent ℝ w := by
        have hperm0 : perm 0 = r₀ := Equiv.swap_apply_left 0 r₀
        have hex : ∀ a : Fin q, ∃ b : Fin q, r₀.succAbove b = perm a.succ := fun a => by
          apply Fin.exists_succAbove_eq
          intro h
          have : perm a.succ = perm 0 := h.trans hperm0.symm
          exact Fin.succ_ne_zero a (perm.injective this)
        let φ : Fin q → Fin q := fun a => Classical.choose (hex a)
        have hφ_eq : ∀ a : Fin q, r₀.succAbove (φ a) = perm a.succ := fun a =>
          Classical.choose_spec (hex a)
        have hφ_inj : Function.Injective φ := fun a₁ a₂ h => by
          have : perm a₁.succ = perm a₂.succ := by rw [← hφ_eq a₁, ← hφ_eq a₂, h]
          exact Fin.succ_injective _ (perm.injective this)
        have hw_eq : w = (fun b : Fin q => v r₀ (r₀.succAbove b)) ∘ φ := by
          ext a j
          change v (perm 0) (perm a.succ) j = v r₀ (r₀.succAbove (φ a)) j
          rw [hperm0, hφ_eq a]
        rw [hw_eq]
        exact hlin.comp φ hφ_inj
      obtain ⟨I0, u0, hI0_inj, hu0_rref, hw_span⟩ := exists_rref q hqd w
      let I : {I : Fin q'.1 → Fin d // Function.Injective I} := ⟨I0, hI0_inj⟩
      have hu_decomp : ∀ x ∈ Submodule.span ℝ (Set.range u0),
          x = ∑ r : Fin q, x (I.1 r) • u0 r := fun x hx => by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨r₀, rfl⟩
          symm
          calc ∑ r : Fin q, u0 r₀ (I.1 r) • u0 r
              = ∑ r : Fin q, (if r₀ = r then (1 : ℝ) else 0) • u0 r := by
                refine Finset.sum_congr rfl fun r _ => by rw [hu0_rref r₀ r]
            _ = u0 r₀ := by simp
        · simp
        · intro x y _ _ hx_eq hy_eq
          calc x + y = (∑ r : Fin q, x (I.1 r) • u0 r) + (∑ r : Fin q, y (I.1 r) • u0 r) := by
                conv_lhs => rw [hx_eq, hy_eq]
            _ = ∑ r : Fin q, (x (I.1 r) + y (I.1 r)) • u0 r := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun r _ => (add_smul _ _ _).symm
            _ = ∑ r : Fin q, (x + y) (I.1 r) • u0 r := rfl
        · intro c x _ hx_eq
          calc c • x = c • ∑ r : Fin q, x (I.1 r) • u0 r := by conv_lhs => rw [hx_eq]
            _ = ∑ r : Fin q, (c * x (I.1 r)) • u0 r := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun r _ => smul_smul c _ _
            _ = ∑ r : Fin q, (c • x) (I.1 r) • u0 r := rfl
      have hk_ex : ∀ a : Fin q, ∃ r : Fin q, w a (I.1 r) ≠ 0 := fun a => by
        by_contra hall
        push Not at hall
        have hwa : w a = 0 := by
          rw [hu_decomp (w a) (hw_span a)]
          exact Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
        exact hv'_nz 0 a.succ (Fin.succ_ne_zero a).symm hwa
      let k₀ : Fin q'.1 → Fin q'.1 := fun a => Classical.choose (hk_ex a)
      have hk₀_ne : ∀ a : Fin q, w a (I.1 (k₀ a)) ≠ 0 := fun a => Classical.choose_spec (hk_ex a)
      let wnorm : Fin q → Ambient d := fun a => (w a (I.1 (k₀ a)))⁻¹ • w a
      have hwnorm_k0 : ∀ a : Fin q, wnorm a (I.1 (k₀ a)) = 1 := fun a => by
        dsimp [wnorm]
        exact inv_mul_cancel₀ (hk₀_ne a)
      have hwnorm_span : ∀ a : Fin q, wnorm a ∈ Submodule.span ℝ (Set.range u0) := fun a =>
        Submodule.smul_mem _ _ (hw_span a)
      have hwnorm_indep : LinearIndependent ℝ wnorm := by
        let units_fn : Fin q → ℝˣ := fun a => Units.mk0 _ (inv_ne_zero (hk₀_ne a))
        have hwnorm_eq : wnorm = fun a => units_fn a • w a := funext fun a => rfl
        rw [hwnorm_eq]
        exact hw_indep.units_smul units_fn
      have hwnorm_ne0 : ∀ a : Fin q, wnorm a ≠ 0 := fun a h => by
        have := hwnorm_k0 a
        rw [h] at this
        simp at this
      have hlin2 : ∀ {a b : Fin q} (hab : a ≠ b) (c₁ c₂ : ℝ),
          c₁ • wnorm a + c₂ • wnorm b = 0 → c₁ = 0 ∧ c₂ = 0 := fun {a b} hab c₁ c₂ hsum => by
        let f : Fin q → ℝ := fun x => if x = a then c₁ else if x = b then c₂ else 0
        have hf : ∑ x : Fin q, f x • wnorm x = 0 := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          have hb_mem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hb_mem]
          have hrest : ∑ x ∈ (Finset.univ.erase a).erase b, f x • wnorm x = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
            have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [f, hxa, hxb]
          rw [hrest, add_zero]
          have ha_v : f a = c₁ := by simp [f]
          have hb_v : f b = c₂ := by simp [f, hab.symm]
          rw [ha_v, hb_v, hsum]
        have h0 := Fintype.linearIndependent_iff.mp hwnorm_indep f hf
        exact ⟨by simpa [f] using h0 a, by simpa [f, hab.symm] using h0 b⟩
      have hlin3 : ∀ {a b c : Fin q}, a ≠ b → b ≠ c → a ≠ c → ∀ c₁ c₂ c₃ : ℝ,
          c₁ • wnorm a + c₂ • wnorm b + c₃ • wnorm c = 0 → c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 :=
          fun {a b c} hab hbc hac c₁ c₂ c₃ hsum => by
        let f : Fin q → ℝ := fun x =>
          if x = a then c₁ else if x = b then c₂ else if x = c then c₃ else 0
        have hf : ∑ x : Fin q, f x • wnorm x = 0 := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          have hb_mem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hb_mem]
          have hc_mem : c ∈ (Finset.univ.erase a).erase b :=
            Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
          rw [← Finset.add_sum_erase _ _ hc_mem]
          have hrest : ∑ x ∈ ((Finset.univ.erase a).erase b).erase c, f x • wnorm x = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxc : x ≠ c := (Finset.mem_erase.mp hx).1
            have hxb : x ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2).1
            simp [f, hxa, hxb, hxc]
          rw [hrest, add_zero]
          have ha_v : f a = c₁ := by simp [f]
          have hb_v : f b = c₂ := by simp [f, hab.symm]
          have hc_v : f c = c₃ := by simp [f, hac.symm, hbc.symm]
          rw [ha_v, hb_v, hc_v]
          rw [← add_assoc]
          exact hsum
        have h0 := Fintype.linearIndependent_iff.mp hwnorm_indep f hf
        exact ⟨by simpa [f] using h0 a,
               by simpa [f, hab.symm] using h0 b,
               by simpa [f, hac.symm, hbc.symm] using h0 c⟩
      have hedge_span : ∀ {a b : Fin q}, a ≠ b →
          ∃ α β : ℝ, v' a.succ b.succ = α • wnorm a + β • wnorm b := fun {a b} hab => by
        obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv'_tri 0 a.succ b.succ
          (Fin.succ_ne_zero a).symm (fun h => hab (Fin.succ_injective _ h))
          (Fin.succ_ne_zero b).symm
        have hc₂ : c₂ ≠ 0 := by
          intro hc2
          rw [hc2, zero_smul, add_zero, hv'_sym 0 b.succ] at hcomb
          change c₁ • v' 0 a.succ + c₃ • (-v' 0 b.succ) = 0 at hcomb
          have hw_comb : (c₁ * w a (I.1 (k₀ a))) • wnorm a + (-c₃ * w b (I.1 (k₀ b))) • wnorm b = 0 := by
            have hwa_eq : w a = w a (I.1 (k₀ a)) • wnorm a := by
              dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne a), one_smul]
            have hwb_eq : w b = w b (I.1 (k₀ b)) • wnorm b := by
              dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne b), one_smul]
            calc (c₁ * w a (I.1 (k₀ a))) • wnorm a + (-c₃ * w b (I.1 (k₀ b))) • wnorm b
                = c₁ • (w a (I.1 (k₀ a)) • wnorm a) + (-c₃) • (w b (I.1 (k₀ b)) • wnorm b) := by
                  simp [mul_smul]
              _ = c₁ • v' 0 a.succ + c₃ • (-v' 0 b.succ) := by
                  rw [← hwa_eq, ← hwb_eq]; simp [w]
              _ = 0 := hcomb
          obtain ⟨h1, h2⟩ := hlin2 hab _ _ hw_comb
          have hc1 : c₁ = 0 := (mul_eq_zero.mp h1).resolve_right (hk₀_ne a)
          have hc3 : c₃ = 0 := neg_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (hk₀_ne b))
          exact hne (by simp [hc1, hc2, hc3])
        refine ⟨(-c₁ / c₂) * w a (I.1 (k₀ a)), (c₃ / c₂) * w b (I.1 (k₀ b)), ?_⟩
        have hwa_eq : w a = w a (I.1 (k₀ a)) • wnorm a := by
          dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne a), one_smul]
        have hwb_eq : w b = w b (I.1 (k₀ b)) • wnorm b := by
          dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne b), one_smul]
        rw [hv'_sym 0 b.succ] at hcomb
        have h1 : c₂ • v' a.succ b.succ = (-c₁) • w a + c₃ • w b := by
          have : c₁ • v' 0 a.succ + c₂ • v' a.succ b.succ + c₃ • (-v' 0 b.succ) = 0 := hcomb
          change c₁ • w a + c₂ • v' a.succ b.succ + c₃ • (-w b) = 0 at this
          rw [smul_neg, ← sub_eq_add_neg] at this
          calc c₂ • v' a.succ b.succ
              = c₂ • v' a.succ b.succ - (c₁ • w a + c₂ • v' a.succ b.succ - c₃ • w b) := by
                rw [this, sub_zero]
            _ = (-c₁) • w a + c₃ • w b := by module
        have h2 : v' a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
        conv_lhs => rw [h2, hwa_eq, hwb_eq]
        module
      let H : Fin q → Fin q → Prop := fun a b =>
        a = b ∨ (v' a.succ b.succ ∉ Submodule.span ℝ {wnorm a} ∧ v' a.succ b.succ ∉ Submodule.span ℝ {wnorm b})
      have H_symm : ∀ a b, H a b → H b a := fun a b hab => by
        rcases hab with rfl | ⟨ha, hb⟩
        · exact Or.inl rfl
        · right
          rw [hv'_sym a.succ b.succ, Submodule.neg_mem_iff, Submodule.neg_mem_iff]
          exact ⟨hb, ha⟩
      have H_pair_coeff : ∀ {a b : Fin q}, a ≠ b → H a b →
          ∃ α β : ℝ, α ≠ 0 ∧ β ≠ 0 ∧ v' a.succ b.succ = α • wnorm a + β • wnorm b := fun {a b} hab hH => by
        rcases hH with h_eq | ⟨hna, hnb⟩
        · exact False.elim (hab h_eq)
        · obtain ⟨α, β, heq⟩ := hedge_span hab
          have hα : α ≠ 0 := by
            intro h0
            apply hnb
            rw [heq, h0, zero_smul, zero_add]
            exact Submodule.smul_mem _ β (Submodule.subset_span rfl)
          have hβ : β ≠ 0 := by
            intro h0
            apply hna
            rw [heq, h0, zero_smul, add_zero]
            exact Submodule.smul_mem _ α (Submodule.subset_span rfl)
          exact ⟨α, β, hα, hβ, heq⟩
      have H_trans : ∀ a b c, H a b → H b c → H a c := fun a b c hab hbc => by
        by_cases h1 : a = b; · subst h1; exact hbc
        by_cases h2 : b = c; · subst h2; exact hab
        by_cases h3 : a = c; · exact Or.inl h3
        obtain ⟨α₁, β₁, hα1, hβ1, heq_ab⟩ := H_pair_coeff h1 hab
        obtain ⟨α₂, β₂, hα2, hβ2, heq_bc⟩ := H_pair_coeff h2 hbc
        obtain ⟨γ, δ, heq_ca⟩ := hedge_span (Ne.symm h3)
        obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv'_tri a.succ b.succ c.succ
          (fin_succ_ne h1) (fin_succ_ne h2) (fin_succ_ne h3)
        have hcomb : (p * α₁ + r₁ * δ) • wnorm a + (p * β₁ + q₁ * α₂) • wnorm b +
            (q₁ * β₂ + r₁ * γ) • wnorm c = 0 := by
          calc (p * α₁ + r₁ * δ) • wnorm a + (p * β₁ + q₁ * α₂) • wnorm b + (q₁ * β₂ + r₁ * γ) • wnorm c
              = p • (α₁ • wnorm a + β₁ • wnorm b) + q₁ • (α₂ • wnorm b + β₂ • wnorm c) +
                  r₁ • (γ • wnorm c + δ • wnorm a) := by module
            _ = p • v' a.succ b.succ + q₁ • v' b.succ c.succ + r₁ • v' c.succ a.succ := by
                rw [heq_ab, heq_bc, heq_ca]
            _ = 0 := htri
        obtain ⟨ha0, hb0, hc0⟩ := hlin3 h1 h2 h3 _ _ _ hcomb
        have hr1 : r₁ ≠ 0 := by
          intro hr0
          rw [hr0, zero_mul, add_zero] at ha0 hc0
          have hp0 : p = 0 := (mul_eq_zero.mp ha0).resolve_right hα1
          have hq0 : q₁ = 0 := (mul_eq_zero.mp hc0).resolve_right hβ2
          exact hpqr (by simp [hp0, hq0, hr0])
        have hp0 : p ≠ 0 := by
          intro hpz
          rw [hpz, zero_mul, zero_add] at ha0 hb0
          have hδ0 : δ = 0 := (mul_eq_zero.mp ha0).resolve_left hr1
          have hq0 : q₁ = 0 := (mul_eq_zero.mp hb0).resolve_right hα2
          rw [hq0, zero_mul, zero_add] at hc0
          have hγ0 : γ = 0 := (mul_eq_zero.mp hc0).resolve_left hr1
          have hv0 : v' c.succ a.succ = 0 := by rw [heq_ca, hγ0, hδ0, zero_smul, zero_smul, add_zero]
          exact hv'_nz c.succ a.succ (fin_succ_ne (Ne.symm h3)) hv0
        have hq0 : q₁ ≠ 0 := by
          intro hqz
          rw [hqz, zero_mul, add_zero] at hb0
          rw [hqz, zero_mul, zero_add] at hc0
          have hpz : p = 0 := (mul_eq_zero.mp hb0).resolve_right hβ1
          exact hp0 hpz
        have hδ_ne : δ ≠ 0 := fun h0 => by
          rw [h0, mul_zero, add_zero] at ha0
          exact hp0 ((mul_eq_zero.mp ha0).resolve_right hα1)
        have hγ_ne : γ ≠ 0 := fun h0 => by
          rw [h0, mul_zero, add_zero] at hc0
          exact hq0 ((mul_eq_zero.mp hc0).resolve_right hβ2)
        have hac_mem : v' a.succ c.succ = (-δ) • wnorm a + (-γ) • wnorm c := by
          rw [hv'_sym c.succ a.succ, heq_ca]; module
        right
        constructor
        · intro hmem
          obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
          have hsub : (-δ - u) • wnorm a + (-γ) • wnorm c = 0 := by
            calc (-δ - u) • wnorm a + (-γ) • wnorm c
                = ((-δ) • wnorm a + (-γ) • wnorm c) - u • wnorm a := by module
              _ = v' a.succ c.succ - v' a.succ c.succ := by rw [← hac_mem, hu]
              _ = 0 := sub_self _
          exact hγ_ne (neg_eq_zero.mp (hlin2 h3 _ _ hsub).2)
        · intro hmem
          obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
          have hsub : (-δ) • wnorm a + (-γ - u) • wnorm c = 0 := by
            calc (-δ) • wnorm a + (-γ - u) • wnorm c
                = ((-δ) • wnorm a + (-γ) • wnorm c) - u • wnorm c := by module
              _ = v' a.succ c.succ - v' a.succ c.succ := by rw [← hac_mem, hu]
              _ = 0 := sub_self _
          exact hδ_ne (neg_eq_zero.mp (hlin2 h3 _ _ hsub).1)
      let root : Fin q'.1 → Fin q'.1 := fun a =>
        (Finset.univ.filter fun b => H a b).min' ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩
      have hroot_H : ∀ a : Fin q, H a (root a) := fun a =>
        (Finset.mem_filter.mp (Finset.min'_mem _ ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩)).2
      have hroot_iff : ∀ a b : Fin q, H a b ↔ root a = root b := fun a b => by
        constructor
        · intro hab
          have hfilt : (Finset.univ.filter fun x => H a x) = (Finset.univ.filter fun x => H b x) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun hax => H_trans b a x (H_symm a b hab) hax, fun hbx => H_trans a b x hab hbx⟩
          dsimp [root]
          congr 1
        · intro heq
          have h1 := hroot_H a
          have h2 := hroot_H b
          rw [← heq] at h2
          exact H_trans a (root a) b h1 (H_symm b (root a) h2)
      have hroot_idem : ∀ a : Fin q, root (root a) = root a := fun a =>
        ((hroot_iff (root a) a).mp (H_symm a (root a) (hroot_H a)))
      have hroot_ex : ∃ a₀ : Fin q'.1, root a₀ = a₀ := by
        let a₁ : Fin q := ⟨0, hq1⟩
        exact ⟨root a₁, hroot_idem a₁⟩
      have ht_all : ∀ a : Fin q, ∃ t : ℝ, (root a ≠ a → t ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧
          wnorm (root a) - t • wnorm a = c • v' (root a).succ a.succ) := fun a => by
        by_cases ha : root a = a
        · exact ⟨1, fun h => absurd ha h⟩
        · obtain ⟨α, β, hα, hβ, heq⟩ := H_pair_coeff ha (H_symm a (root a) (hroot_H a))
          refine ⟨-β / α, fun _ => ⟨div_ne_zero (neg_ne_zero.mpr hβ) hα, α⁻¹, inv_ne_zero hα, ?_⟩⟩
          have hc : -(-β / α) = α⁻¹ * β := by field_simp [hα]
          calc wnorm (root a) - (-β / α) • wnorm a
              = wnorm (root a) + (α⁻¹ * β) • wnorm a := by rw [sub_eq_add_neg, ← neg_smul, hc]
            _ = α⁻¹ • (α • wnorm (root a) + β • wnorm a) := by
                rw [smul_add, mul_smul]
                congr 1
                rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
            _ = α⁻¹ • v' (root a).succ a.succ := by rw [heq]
      choose t_val ht_spec using ht_all
      let useLeft : Pairs q'.1 → Bool := fun p =>
        decide (v' p.1.1.succ p.1.2.succ ∈ Submodule.span ℝ {wnorm p.1.1})
      let sh0 : TreeShape d 0 := .star q' perm I k₀ root useLeft
      have hsh0_val : sh0.Valid := ⟨hq1, hqd, hroot_ex⟩
      let θ0 : sh0.ParamIdx → ℝ :=
        Sum.elim (fun p => u0 p.1 p.2.1)
          (Sum.elim (fun p => wnorm p.1 (I.1 p.2.1)) (fun p => t_val p.1))
      have hu_eq_u0 : ∀ r : Fin q,
          (∑ j : Fin d,
            (if hj : ∀ s : Fin q'.1, I.1 s ≠ j then
              θ0 (Sum.inl (r, ⟨j, hj⟩))
            else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = u0 r := fun r => by
        ext j
        have hsum_apply : ∀ (s : Finset (Fin d)) (g : Fin d → Ambient d),
            (∑ k ∈ s, g k) j = ∑ k ∈ s, g k j := fun s g => by
          induction s using Finset.induction with
          | empty => simp
          | insert _ _ h ih => simp [Finset.sum_insert h, ih]
        rw [hsum_apply]
        have hsingle : ∀ k : Fin d,
            (if hk : ∀ s : Fin q'.1, I.1 s ≠ k then
              θ0 (Sum.inl (r, ⟨k, hk⟩))
            else if I.1 r = k then (1 : ℝ) else 0) * (EuclideanSpace.single k (1 : ℝ)) j =
            if k = j then
              (if hk : ∀ s : Fin q'.1, I.1 s ≠ k then
                θ0 (Sum.inl (r, ⟨k, hk⟩))
              else if I.1 r = k then (1 : ℝ) else 0)
            else 0 := fun k => by
          by_cases hkj : k = j
          · subst hkj; simp [EuclideanSpace.single]
          · simp [EuclideanSpace.single, hkj, Ne.symm hkj]
        simp only [PiLp.smul_apply, smul_eq_mul, hsingle, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        split_ifs with hj hrs
        · rfl
        · rw [← hrs, hu0_rref r r]; simp
        · push Not at hj
          obtain ⟨s, hs⟩ := hj
          subst hs
          rw [hu0_rref r s]
          have hne : r ≠ s := fun h => hrs (congrArg I.1 h)
          simp [hne]
      have hw_eq_wnorm : ∀ a : Fin q,
          (∑ r : Fin q'.1,
            (if hr : r = k₀ a then (1 : ℝ) else θ0 (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) •
            (∑ j : Fin d,
              (if hj : ∀ s : Fin q'.1, I.1 s ≠ j then
                θ0 (Sum.inl (r, ⟨j, hj⟩))
              else if I.1 r = j then (1 : ℝ) else 0) •
              EuclideanSpace.single j (1 : ℝ))) = wnorm a := fun a => by
        calc _ = ∑ r : Fin q, (if hr : r = k₀ a then (1 : ℝ) else θ0 (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) • u0 r := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_eq_u0 r]
          _ = ∑ r : Fin q, wnorm a (I.1 r) • u0 r := by
              refine Finset.sum_congr rfl fun r _ => ?_
              by_cases hr : r = k₀ a
              · subst hr; simp only [↓reduceDIte, hwnorm_k0]
              · simp only [hr, ↓reduceDIte, θ0]; rfl
          _ = wnorm a := (hu_decomp (wnorm a) (hwnorm_span a)).symm
      have hrep0 : ∀ e : Pairs (sh0.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
          sh0.evalEdges θ0 e = c • v e.1.1 e.1.2 := fun e => by
        change ∃ c : ℝ, c ≠ 0 ∧ evalStar q' perm I k₀ root useLeft θ0 e = c • v e.1.1 e.1.2
        let t_fun : Fin q → ℝ := fun a =>
          if ha : root a = a then 1 else θ0 (Sum.inr (Sum.inr ⟨a, ha⟩))
        have ht_fun_spec : ∀ a : Fin q, t_fun a = if root a = a then 1 else t_val a := fun a => by
          dsimp [t_fun]; split_ifs <;> rfl
        have hperm_ne : perm.symm e.1.1 ≠ perm.symm e.1.2 := fun h =>
          Fin.ne_of_lt e.2 (perm.symm.injective h)
        have hve_eq : v e.1.1 e.1.2 = v' (perm.symm e.1.1) (perm.symm e.1.2) := by
          dsimp [v']
          congr 1 <;> exact (perm.apply_symm_apply _).symm
        rw [hve_eq]
        unfold evalStar
        dsimp only
        simp_rw [hw_eq_wnorm]
        induction hpi : perm.symm e.1.1 using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          induction hpj : perm.symm e.1.2 using Fin.cases with
          | zero => exact False.elim (hperm_ne (hpi.trans hpj.symm))
          | succ b =>
            simp only [Fin.cases_succ]
            refine ⟨(w b (I.1 (k₀ b)))⁻¹, inv_ne_zero (hk₀_ne b), ?_⟩
            rfl
        | succ a =>
          simp only [Fin.cases_succ]
          induction hpj : perm.symm e.1.2 using Fin.cases with
          | zero =>
            simp only [Fin.cases_zero]
            refine ⟨(w a (I.1 (k₀ a)))⁻¹, inv_ne_zero (hk₀_ne a), ?_⟩
            rw [hv'_sym 0 a.succ, smul_neg]
          | succ b =>
            simp only [Fin.cases_succ]
            have hab : a ≠ b := fun h => hperm_ne (by rw [hpi, hpj, h])
            by_cases hrab : root a = root b
            · rw [if_pos hrab]
              have hHab : H a b := (hroot_iff a b).mpr hrab
              change ∃ c : ℝ, c ≠ 0 ∧ t_fun a • wnorm a - t_fun b • wnorm b = c • v' a.succ b.succ
              by_cases har : root a = a
              · have hbr : root b ≠ b := fun h => hab (by rw [← har, hrab, h])
                obtain ⟨ht_ne, c, hc, hce⟩ := ht_spec b hbr
                have htf_a : t_fun a = 1 := by rw [ht_fun_spec, if_pos har]
                have htf_b : t_fun b = t_val b := by rw [ht_fun_spec, if_neg hbr]
                have hrb : root b = a := hrab.symm.trans har
                rw [hrb] at hce
                refine ⟨c, hc, ?_⟩
                rw [htf_a, htf_b, one_smul, hce]
              · by_cases hbr : root b = b
                · obtain ⟨ht_ne, c, hc, hce⟩ := ht_spec a har
                  have htf_a : t_fun a = t_val a := by rw [ht_fun_spec, if_neg har]
                  have htf_b : t_fun b = 1 := by rw [ht_fun_spec, if_pos hbr]
                  have hra : root a = b := hrab.trans hbr
                  rw [hra] at hce
                  refine ⟨c, hc, ?_⟩
                  rw [htf_a, htf_b, one_smul]
                  calc t_val a • wnorm a - wnorm b = -(wnorm b - t_val a • wnorm a) := by module
                    _ = -(c • v' b.succ a.succ) := by rw [hce]
                    _ = c • v' a.succ b.succ := by rw [hv'_sym a.succ b.succ]; module
                · let r := root a
                  have hr_b : root b = r := hrab.symm
                  obtain ⟨ta_ne, ca, hca, hcea⟩ := ht_spec a har
                  obtain ⟨tb_ne, cb, hcb, hceb⟩ := ht_spec b hbr
                  have htf_a : t_fun a = t_val a := by rw [ht_fun_spec, if_neg har]
                  have htf_b : t_fun b = t_val b := by rw [ht_fun_spec, if_neg hbr]
                  rw [htf_a, htf_b]
                  obtain ⟨γ, δ, hγ, hδ, heq_ab⟩ := H_pair_coeff hab hHab
                  have har_ne : r ≠ a := fun h => har h
                  have hbr_ne : r ≠ b := fun h => hbr (hr_b.trans h)
                  obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv'_tri r.succ a.succ b.succ
                    (fin_succ_ne har_ne) (fin_succ_ne hab)
                    (fin_succ_ne hbr_ne)
                  have hva : v' r.succ a.succ = ca⁻¹ • (wnorm r - t_val a • wnorm a) := by
                    rw [hcea, smul_smul, inv_mul_cancel₀ hca, one_smul]
                  have hvb : v' b.succ r.succ = -(cb⁻¹ • (wnorm r - t_val b • wnorm b)) := by
                    rw [hv'_sym r.succ b.succ, ← hr_b, hceb, smul_smul, inv_mul_cancel₀ hcb, one_smul]
                  have hcomb : (p * ca⁻¹ - r₁ * cb⁻¹) • wnorm r +
                      (-p * ca⁻¹ * t_val a + q₁ * γ) • wnorm a +
                      (r₁ * cb⁻¹ * t_val b + q₁ * δ) • wnorm b = 0 := by
                    calc _ = p • (ca⁻¹ • (wnorm r - t_val a • wnorm a)) +
                              q₁ • (γ • wnorm a + δ • wnorm b) +
                              r₁ • (-(cb⁻¹ • (wnorm r - t_val b • wnorm b))) := by module
                      _ = p • v' r.succ a.succ + q₁ • v' a.succ b.succ + r₁ • v' b.succ r.succ := by
                          rw [← hva, ← heq_ab, ← hvb]
                      _ = 0 := htri
                  obtain ⟨hr0, ha0, hb0⟩ := hlin3 har_ne hab hbr_ne _ _ _ hcomb
                  have hpr : p * ca⁻¹ = r₁ * cb⁻¹ := sub_eq_zero.mp hr0
                  have hq₁ : q₁ ≠ 0 := fun hqz => by
                    rw [hqz, zero_mul, add_zero] at ha0 hb0
                    have hpz : p = 0 := by
                      rcases mul_eq_zero.mp ha0 with h1 | h1
                      · rcases mul_eq_zero.mp h1 with h2 | h2
                        · exact neg_eq_zero.mp h2
                        · exact False.elim (inv_ne_zero hca h2)
                      · exact False.elim (ta_ne h1)
                    have hrz : r₁ = 0 := by
                      rw [hpz, zero_mul] at hpr
                      exact (mul_eq_zero.mp hpr.symm).resolve_right (inv_ne_zero hcb)
                    exact hpqr (by simp [hpz, hqz, hrz])
                  have hp_ne : p ≠ 0 := fun hpz => by
                    rw [hpz, neg_zero, zero_mul, zero_mul, zero_add] at ha0
                    exact hγ ((mul_eq_zero.mp ha0).resolve_left hq₁)
                  have hden : p * ca⁻¹ ≠ 0 := mul_ne_zero hp_ne (inv_ne_zero hca)
                  refine ⟨q₁ / (p * ca⁻¹), div_ne_zero hq₁ hden, ?_⟩
                  have hγ_eq : q₁ * γ = (p * ca⁻¹) * t_val a := by linarith
                  have hδ_eq : q₁ * δ = -((p * ca⁻¹) * t_val b) := by rw [hpr]; linarith
                  have heq_v : (q₁ / (p * ca⁻¹)) • v' a.succ b.succ =
                      (q₁ / (p * ca⁻¹)) • (γ • wnorm a + δ • wnorm b) := by rw [heq_ab]
                  have ht1 : (q₁ / (p * ca⁻¹)) * γ = t_val a := by
                    calc (q₁ / (p * ca⁻¹)) * γ = (q₁ * γ) / (p * ca⁻¹) := by ring
                      _ = ((p * ca⁻¹) * t_val a) / (p * ca⁻¹) := by rw [hγ_eq]
                      _ = t_val a := mul_div_cancel_left₀ _ hden
                  have ht2 : (q₁ / (p * ca⁻¹)) * δ = -t_val b := by
                    calc (q₁ / (p * ca⁻¹)) * δ = (q₁ * δ) / (p * ca⁻¹) := by ring
                      _ = (-((p * ca⁻¹) * t_val b)) / (p * ca⁻¹) := by rw [hδ_eq]
                      _ = -t_val b := by rw [neg_div, mul_div_cancel_left₀ _ hden]
                  have hlhs_eq : (q₁ / (p * ca⁻¹)) • (γ • wnorm a + δ • wnorm b) =
                      t_val a • wnorm a - t_val b • wnorm b := by
                    rw [smul_add, sub_eq_add_neg]
                    congr 1
                    · rw [smul_smul, ht1]
                    · rw [smul_smul, ht2, neg_smul]
                  rw [heq_v, hlhs_eq]
            · rw [if_neg hrab]
              have hnH : ¬ H a b := fun h => hrab ((hroot_iff a b).mp h)
              have hmem_or : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} ∨
                  v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := by
                dsimp [H] at hnH
                push Not at hnH
                by_cases hmem_a : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a}
                · exact Or.inl hmem_a
                · exact Or.inr (hnH.2 hmem_a)
              rcases lt_or_gt_of_ne hab with hlt | hgt
              · simp only [hlt, ↓reduceDIte]
                by_cases huL : useLeft ⟨(a, b), hlt⟩ = true
                · simp only [huL, ↓reduceIte]
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} := by
                    simpa [useLeft] using huL
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
                · simp only [huL, Bool.false_eq_true, ↓reduceIte]
                  have hna : v' a.succ b.succ ∉ Submodule.span ℝ {wnorm a} := by
                    simpa [useLeft] using huL
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := hmem_or.resolve_left hna
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
              · have hnot : ¬ a < b := Nat.not_lt.mpr hgt.le
                simp only [hnot, ↓reduceDIte, hgt]
                by_cases huL : useLeft ⟨(b, a), hgt⟩ = true
                · simp only [huL, ↓reduceIte]
                  have hmem_ba : v' b.succ a.succ ∈ Submodule.span ℝ {wnorm b} := by
                    simpa [useLeft] using huL
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := by
                    rwa [hv'_sym a.succ b.succ, Submodule.neg_mem_iff] at hmem_ba
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
                · simp only [huL, Bool.false_eq_true, ↓reduceIte]
                  have hnb_ba : v' b.succ a.succ ∉ Submodule.span ℝ {wnorm b} := by
                    simpa [useLeft] using huL
                  have hnb : v' a.succ b.succ ∉ Submodule.span ℝ {wnorm b} := fun h =>
                    hnb_ba (by rw [hv'_sym a.succ b.succ, Submodule.neg_mem_iff]; exact h)
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} := hmem_or.resolve_right hnb
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact exists_liftShape q (Nat.zero_le q) sh0 hsh0_val
        (fun e => v e.1.1 e.1.2) ⟨θ0, hrep0⟩
    · push Not at hstar
      let w : Fin q → Ambient d := fun a => v 0 a.succ
      have hw_not_indep : ¬ LinearIndependent ℝ w := by
        have h := hstar 0
        have hw_eq : w = fun a : Fin q => v 0 ((0 : Fin (q + 1)).succAbove a) := rfl
        rwa [hw_eq]
      have hq2 : 2 ≤ q := by
        by_contra hlt2
        have hq_eq1 : q = 1 := by omega
        subst hq_eq1
        apply hw_not_indep
        refine Fintype.linearIndependent_iff.mpr fun g hg a => ?_
        have ha0 : a = 0 := Fin.eq_zero a
        subst ha0
        rw [Fin.sum_univ_one] at hg
        exact (smul_eq_zero.mp hg).resolve_right (hv_nz 0 1 (by decide))
      let U : Submodule ℝ (Ambient d) := Submodule.span ℝ (Set.range w)
      have hU_lt_q : Module.finrank ℝ U < q := by
        have hle : Module.finrank ℝ U ≤ q := by
          have h1 : Module.finrank ℝ U ≤ (Set.range w).toFinset.card :=
            finrank_span_le_card (Set.range w)
          have h2 : (Set.range w).toFinset.card ≤ q := by
            calc (Set.range w).toFinset.card = (Finset.univ.image w).card := by
                  congr 1; ext x; simp
              _ ≤ Finset.univ.card := Finset.card_image_le
              _ = q := Fintype.card_fin q
          exact h1.trans h2
        refine lt_of_le_of_ne hle fun hfin => hw_not_indep ?_
        rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
        exact hfin.symm
      let cls_raw : Fin q → Fin q := fun a =>
        (Finset.univ.filter fun b => Submodule.span ℝ {w a} = Submodule.span ℝ {w b}).min'
          ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have hcls_raw_mem : ∀ a : Fin q,
          Submodule.span ℝ {w a} = Submodule.span ℝ {w (cls_raw a)} := fun a =>
        (Finset.mem_filter.mp ((Finset.univ.filter fun b =>
          Submodule.span ℝ {w a} = Submodule.span ℝ {w b}).min'_mem
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩)).2
      have hcls_raw_iff : ∀ a b : Fin q,
          cls_raw a = cls_raw b ↔ Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := fun a b => by
        constructor
        · intro h
          rw [hcls_raw_mem a, hcls_raw_mem b, h]
        · intro h
          have hfilt : (Finset.univ.filter fun x => Submodule.span ℝ {w a} = Submodule.span ℝ {w x}) =
              (Finset.univ.filter fun x => Submodule.span ℝ {w b} = Submodule.span ℝ {w x}) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
          dsimp [cls_raw]
          congr 1
      have hcls_raw_idem : ∀ a : Fin q, cls_raw (cls_raw a) = cls_raw a := fun a =>
        (hcls_raw_iff (cls_raw a) a).mpr (hcls_raw_mem a).symm
      let roots : Finset (Fin q) := Finset.univ.image cls_raw
      obtain ⟨s, hs_eq⟩ : ∃ s : ℕ, s = roots.card := ⟨roots.card, rfl⟩
      have hs1 : 1 ≤ s := hs_eq.symm ▸
        Finset.card_pos.mpr ⟨cls_raw ⟨0, hq1⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      let ordRoots : Fin s ≃o roots := roots.orderIsoOfFin hs_eq.symm
      let cls : Fin q → Fin s := fun a =>
        ordRoots.symm ⟨cls_raw a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
      have hcls_iff : ∀ a b : Fin q,
          cls a = cls b ↔ Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := fun a b => by
        rw [← hcls_raw_iff a b]
        constructor
        · intro h
          have : (⟨cls_raw a, _⟩ : roots) = ⟨cls_raw b, _⟩ := ordRoots.symm.injective h
          exact congrArg Subtype.val this
        · intro h
          apply congrArg (ordRoots.symm)
          exact Subtype.ext h
      let rep : Fin s → Fin q := fun r => (ordRoots r).1
      have hcls_rep : ∀ r : Fin s, cls (rep r) = r := fun r => by
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (ordRoots r).2
        have hraw : cls_raw (rep r) = rep r := by
          dsimp [rep]; rw [← hb, hcls_raw_idem b]
        dsimp [cls]
        have : (⟨cls_raw (rep r), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ : roots) = ordRoots r :=
          Subtype.ext hraw
        rw [this, OrderIso.symm_apply_apply]
      have hC_ge1 : ∀ r : Fin s, 1 ≤ (classSet q s cls r).card := fun r =>
        Finset.card_pos.mpr ⟨rep r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls_rep r⟩⟩
      let V : Fin s → Submodule ℝ (Ambient d) := fun r =>
        Submodule.span ℝ {x : Ambient d |
          ∃ a ∈ classSet q s cls r, ∃ b ∈ classSet q s cls r, a ≠ b ∧ x = v a.succ b.succ}
      have hV_finrank : ∀ r : Fin s,
          Module.finrank ℝ (V r) ≤ (classSet q s cls r).card - 1 := fun r =>
        finrank_triangle_span_le (fun a b => v a.succ b.succ)
          (fun a b => hv_sym a.succ b.succ)
          (fun a b hab => hv_nz a.succ b.succ (fin_succ_ne hab))
          (fun a b c hab hbc hac => by
            obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri a.succ b.succ c.succ
              (fin_succ_ne hab) (fin_succ_ne hbc) (fin_succ_ne hac)
            refine ⟨c₁, c₂, c₃, ?_, hcomb⟩
            by_contra hall
            push Not at hall
            exact hne (Prod.ext hall.1 (Prod.ext hall.2.1 hall.2.2)))
          (classSet q s cls r).card (classSet q s cls r)
          ⟨rep r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls_rep r⟩⟩ rfl
      have hU_eq_rep : U = Submodule.span ℝ (Set.range fun r : Fin s => w (rep r)) := by
        refine le_antisymm ?_ ?_
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨a, rfl⟩
          have hsp : w a ∈ Submodule.span ℝ {w (rep (cls a))} := by
            rw [← (hcls_iff a (rep (cls a))).mp (hcls_rep (cls a)).symm]
            exact Submodule.subset_span rfl
          exact Submodule.span_mono (by
            rintro _ rfl
            exact ⟨cls a, rfl⟩) hsp
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact Submodule.subset_span ⟨rep r, rfl⟩
      have hU_finrank_le : Module.finrank ℝ U ≤ s := by
        rw [hU_eq_rep]
        have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range fun r : Fin s => w (rep r))) ≤
            (Set.range fun r : Fin s => w (rep r)).toFinset.card :=
          finrank_span_le_card _
        have h2 : (Set.range fun r : Fin s => w (rep r)).toFinset.card ≤ s := by
          calc (Set.range fun r : Fin s => w (rep r)).toFinset.card
              = (Finset.univ.image fun r : Fin s => w (rep r)).card := by
                congr 1; ext x; simp
            _ ≤ Finset.univ.card := Finset.card_image_le
            _ = s := Fintype.card_fin s
        exact h1.trans h2
      let W_sup : Submodule ℝ (Ambient d) := Finset.univ.sup V
      let W_top : Submodule ℝ (Ambient d) := U ⊔ W_sup
      have hW_sub : Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q + 1), x = v i j} ≤ W_top := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, j, rfl⟩
        rw [SetLike.mem_coe]
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero =>
            have hv00 : v 0 0 = 0 := by
              have h := hv_sym 0 0
              have : (2 : ℝ) • v 0 0 = 0 := by
                calc (2 : ℝ) • v 0 0 = v 0 0 + v 0 0 := two_smul ℝ _
                  _ = v 0 0 + (- v 0 0) := by conv_lhs => rhs; rw [h]
                  _ = 0 := add_neg_cancel _
              exact (smul_eq_zero.mp this).resolve_left two_ne_zero
            rw [hv00]
            exact Submodule.zero_mem _
          | succ b => exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩)
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            rw [hv_sym 0 a.succ]
            exact Submodule.neg_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))
          | succ b =>
            by_cases hab : a = b
            · subst hab
              have hvaa : v a.succ a.succ = 0 := by
                have h := hv_sym a.succ a.succ
                have : (2 : ℝ) • v a.succ a.succ = 0 := by
                  calc (2 : ℝ) • v a.succ a.succ = v a.succ a.succ + v a.succ a.succ := two_smul ℝ _
                    _ = v a.succ a.succ + (- v a.succ a.succ) := by conv_lhs => rhs; rw [h]
                    _ = 0 := add_neg_cancel _
                exact (smul_eq_zero.mp this).resolve_left two_ne_zero
              rw [hvaa]
              exact Submodule.zero_mem _
            · by_cases hcls : cls a = cls b
              · refine Submodule.mem_sup_right ?_
                have hle : V (cls a) ≤ (Finset.univ.sup V : Submodule ℝ (Ambient d)) :=
                  Finset.le_sup (Finset.mem_univ (cls a))
                apply hle
                exact Submodule.subset_span ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
                  b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩, hab, rfl⟩
              · obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri 0 a.succ b.succ
                  (Fin.succ_ne_zero a).symm (fin_succ_ne hab) (Fin.succ_ne_zero b).symm
                have hc₂ : c₂ ≠ 0 := by
                  intro hc2
                  rw [hc2, zero_smul, add_zero, hv_sym 0 b.succ] at hcomb
                  have hspan_eq : Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := by
                    have hwa0 : w a ≠ 0 := hv_nz 0 a.succ (Fin.succ_ne_zero a).symm
                    have hwb0 : w b ≠ 0 := hv_nz 0 b.succ (Fin.succ_ne_zero b).symm
                    have hc13 : c₁ • w a = c₃ • w b := by
                      have : c₁ • w a + c₃ • (-w b) = 0 := hcomb
                      rw [smul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
                      exact this
                    have hc1_ne : c₁ ≠ 0 := fun h1 => by
                      rw [h1, zero_smul] at hc13
                      have hc3_ne : c₃ ≠ 0 := fun h3 => hne (by simp [h1, hc2, h3])
                      exact hwb0 ((smul_eq_zero.mp hc13.symm).resolve_left hc3_ne)
                    have hc3_ne : c₃ ≠ 0 := fun h3 => by
                      rw [h3, zero_smul] at hc13
                      exact hwa0 ((smul_eq_zero.mp hc13).resolve_left hc1_ne)
                    refine le_antisymm ?_ ?_
                    · refine Submodule.span_le.mpr ?_
                      rintro _ rfl
                      have : w a = (c₁⁻¹ * c₃) • w b := by
                        rw [mul_smul, ← hc13, smul_smul, inv_mul_cancel₀ hc1_ne, one_smul]
                      rw [SetLike.mem_coe, this]
                      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
                    · refine Submodule.span_le.mpr ?_
                      rintro _ rfl
                      have : w b = (c₃⁻¹ * c₁) • w a := by
                        rw [mul_smul, hc13, smul_smul, inv_mul_cancel₀ hc3_ne, one_smul]
                      rw [SetLike.mem_coe, this]
                      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
                  exact hcls ((hcls_iff a b).mpr hspan_eq)
                refine Submodule.mem_sup_left ?_
                have hv_eq : v a.succ b.succ = (-c₁ / c₂) • w a + (c₃ / c₂) • w b := by
                  rw [hv_sym 0 b.succ] at hcomb
                  have h1 : c₂ • v a.succ b.succ = (-c₁) • w a + c₃ • w b := by
                    change c₁ • w a + c₂ • v a.succ b.succ + c₃ • (-w b) = 0 at hcomb
                    rw [smul_neg, ← sub_eq_add_neg] at hcomb
                    calc c₂ • v a.succ b.succ
                        = c₂ • v a.succ b.succ - (c₁ • w a + c₂ • v a.succ b.succ - c₃ • w b) := by
                          rw [hcomb, sub_zero]
                      _ = (-c₁) • w a + c₃ • w b := by module
                  have h2 : v a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
                    rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
                  rw [h2]; module
                rw [hv_eq]
                exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
                  (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      have hsup_le : ∀ T : Finset (Fin s),
          Module.finrank ℝ ((T.sup V : Submodule ℝ (Ambient d))) ≤ ∑ r ∈ T, Module.finrank ℝ (V r) := fun T => by
        induction T using Finset.induction with
        | empty => simp
        | insert r T hr ihT =>
          rw [Finset.sup_insert, Finset.sum_insert hr]
          exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add_right ihT _)
      have hfib_q : ∑ r : Fin s, (classSet q s cls r).card = q := by
        have h := Finset.card_eq_sum_card_fiberwise (f := cls) (s := Finset.univ) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (cls a))
        simpa [classSet] using h.symm
      have hsum_sub_q : s + ∑ r : Fin s, ((classSet q s cls r).card - 1) = q := by
        have h1 : ∑ r : Fin s, (classSet q s cls r).card =
            ∑ r : Fin s, (1 + ((classSet q s cls r).card - 1)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hcr := hC_ge1 r
          omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one] at hfib_q
        exact hfib_q
      have hsandwich_top : q ≤ Module.finrank ℝ W_top :=
        hv_dim.trans (Submodule.finrank_mono hW_sub)
      have hW_sup_le : Module.finrank ℝ W_sup ≤ ∑ r : Fin s, Module.finrank ℝ (V r) :=
        hsup_le Finset.univ
      have hsandwich_sum : Module.finrank ℝ W_top ≤
          Module.finrank ℝ U + ∑ r : Fin s, Module.finrank ℝ (V r) :=
        (Submodule.finrank_add_le_finrank_add_finrank U W_sup).trans
          (Nat.add_le_add_left hW_sup_le _)
      have hsum_V_le : ∑ r : Fin s, Module.finrank ℝ (V r) ≤
          ∑ r : Fin s, ((classSet q s cls r).card - 1) :=
        Finset.sum_le_sum fun r _ => hV_finrank r
      have hU_finrank : Module.finrank ℝ U = s := by omega
      have hs_lt_q : s < q := by omega
      have hV_finrank_eq : ∀ r : Fin s, Module.finrank ℝ (V r) = (classSet q s cls r).card - 1 := fun r => by
        by_contra hne
        have hlt : Module.finrank ℝ (V r) < (classSet q s cls r).card - 1 :=
          lt_of_le_of_ne (hV_finrank r) hne
        have hsum_lt : ∑ x : Fin s, Module.finrank ℝ (V x) <
            ∑ x : Fin s, ((classSet q s cls x).card - 1) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
          conv_rhs => rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
          exact add_lt_add_of_lt_of_le hlt
            (Finset.sum_le_sum fun x _ => hV_finrank x)
        omega
      have hUV_disj : ∀ r : Fin s, U ⊓ V r = ⊥ := fun r => by
        let T_erase : Submodule ℝ (Ambient d) := (Finset.univ.erase r).sup V
        let T0 : Submodule ℝ (Ambient d) := U ⊔ T_erase
        have hT0_sup : T0 ⊔ V r = W_top := by
          have hpart : Finset.univ = insert r (Finset.univ.erase r) :=
            (Finset.insert_erase (Finset.mem_univ r)).symm
          have hsup_eq : V r ⊔ T_erase = W_sup := by
            dsimp [W_sup, T_erase]
            rw [← Finset.sup_insert, ← hpart]
          dsimp [T0, W_top]
          rw [sup_assoc, sup_comm T_erase (V r), hsup_eq]
        have hT0_finrank : Module.finrank ℝ T0 + Module.finrank ℝ (V r) ≤ q := by
          have hT_erase_le : Module.finrank ℝ T_erase ≤
              ∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x) :=
            hsup_le (Finset.univ.erase r)
          have h1 : Module.finrank ℝ T0 ≤ Module.finrank ℝ U + ∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x) :=
            (Submodule.finrank_add_le_finrank_add_finrank U T_erase).trans
              (Nat.add_le_add_left hT_erase_le _)
          have h2 : (∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x)) + Module.finrank ℝ (V r) =
              ∑ x : Fin s, Module.finrank ℝ (V x) := by
            rw [add_comm, Finset.add_sum_erase Finset.univ (fun x => Module.finrank ℝ (V x)) (Finset.mem_univ r)]
          omega
        let T0_inter : Submodule ℝ (Ambient d) := T0 ⊓ V r
        have hinf0 : Module.finrank ℝ T0_inter = 0 := by
          have hadd := Submodule.finrank_sup_add_finrank_inf_eq T0 (V r)
          rw [hT0_sup] at hadd
          change Module.finrank ℝ W_top + Module.finrank ℝ T0_inter =
            Module.finrank ℝ T0 + Module.finrank ℝ (V r) at hadd
          omega
        have hbot : T0_inter = ⊥ := Submodule.finrank_eq_zero.mp hinf0
        exact le_bot_iff.mp (by rw [← hbot]; exact inf_le_inf_right _ le_sup_left)
      have hcross_in_U : ∀ a b : Fin q, cls a ≠ cls b → v a.succ b.succ ∈ U := fun a b hcls => by
        obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri 0 a.succ b.succ
          (Fin.succ_ne_zero a).symm (fin_succ_ne (fun h => hcls (congrArg cls h)))
          (Fin.succ_ne_zero b).symm
        have hc₂ : c₂ ≠ 0 := by
          intro hc2
          rw [hc2, zero_smul, add_zero, hv_sym 0 b.succ] at hcomb
          have hspan_eq : Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := by
            have hwa0 : w a ≠ 0 := hv_nz 0 a.succ (Fin.succ_ne_zero a).symm
            have hwb0 : w b ≠ 0 := hv_nz 0 b.succ (Fin.succ_ne_zero b).symm
            have hc13 : c₁ • w a = c₃ • w b := by
              have : c₁ • w a + c₃ • (-w b) = 0 := hcomb
              rw [smul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
              exact this
            have hc1_ne : c₁ ≠ 0 := fun h1 => by
              rw [h1, zero_smul] at hc13
              have hc3_ne : c₃ ≠ 0 := fun h3 => hne (by simp [h1, hc2, h3])
              exact hwb0 ((smul_eq_zero.mp hc13.symm).resolve_left hc3_ne)
            have hc3_ne : c₃ ≠ 0 := fun h3 => by
              rw [h3, zero_smul] at hc13
              exact hwa0 ((smul_eq_zero.mp hc13).resolve_left hc1_ne)
            refine le_antisymm ?_ ?_
            · refine Submodule.span_le.mpr ?_
              rintro _ rfl
              have : w a = (c₁⁻¹ * c₃) • w b := by
                rw [mul_smul, ← hc13, smul_smul, inv_mul_cancel₀ hc1_ne, one_smul]
              rw [SetLike.mem_coe, this]
              exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
            · refine Submodule.span_le.mpr ?_
              rintro _ rfl
              have : w b = (c₃⁻¹ * c₁) • w a := by
                rw [mul_smul, hc13, smul_smul, inv_mul_cancel₀ hc3_ne, one_smul]
              rw [SetLike.mem_coe, this]
              exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
          exact hcls ((hcls_iff a b).mpr hspan_eq)
        have hv_eq : v a.succ b.succ = (-c₁ / c₂) • w a + (c₃ / c₂) • w b := by
          rw [hv_sym 0 b.succ] at hcomb
          have h1 : c₂ • v a.succ b.succ = (-c₁) • w a + c₃ • w b := by
            change c₁ • w a + c₂ • v a.succ b.succ + c₃ • (-w b) = 0 at hcomb
            rw [smul_neg, ← sub_eq_add_neg] at hcomb
            calc c₂ • v a.succ b.succ
                = c₂ • v a.succ b.succ - (c₁ • w a + c₂ • v a.succ b.succ - c₃ • w b) := by
                  rw [hcomb, sub_zero]
              _ = (-c₁) • w a + c₃ • w b := by module
          have h2 : v a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
            rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
          rw [h2]; module
        rw [hv_eq]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      have hcross_step : ∀ {a a' b : Fin q}, cls a = cls a' → cls a ≠ cls b →
          ∃ c : ℝ, c ≠ 0 ∧ v a'.succ b.succ = c • v a.succ b.succ := fun {a a' b} haa' hab => by
        by_cases ha : a = a'
        · subst ha; exact ⟨1, one_ne_zero, (one_smul ℝ _).symm⟩
        · obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv_tri a.succ a'.succ b.succ
            (fin_succ_ne ha)
            (fin_succ_ne (fun h => hab (haa'.trans (congrArg cls h))))
            (fin_succ_ne (fun h => hab (congrArg cls h)))
          have hVmem : p • v a.succ a'.succ ∈ V (cls a) :=
            Submodule.smul_mem _ p (Submodule.subset_span ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
              a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, haa'.symm⟩, ha, rfl⟩)
          have hUmem : r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ ∈ U := by
            refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hcross_in_U a b hab)) ?_
            exact Submodule.smul_mem _ _ (hcross_in_U a' b (haa' ▸ hab))
          have heq : p • v a.succ a'.succ = r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ := by
            rw [hv_sym a.succ b.succ] at htri
            calc p • v a.succ a'.succ
                = p • v a.succ a'.succ - (p • v a.succ a'.succ + q₁ • v a'.succ b.succ + r₁ • (-v a.succ b.succ)) := by
                  rw [htri, sub_zero]
              _ = r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ := by module
          have h0 : p • v a.succ a'.succ = 0 := by
            have hmem : p • v a.succ a'.succ ∈ U ⊓ V (cls a) :=
              ⟨heq ▸ hUmem, hVmem⟩
            rw [hUV_disj (cls a), Submodule.mem_bot] at hmem
            exact hmem
          have hp0 : p = 0 := (smul_eq_zero.mp h0).resolve_right (hv_nz a.succ a'.succ (fin_succ_ne ha))
          have heq0 : r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ = 0 := by rw [← heq, h0]
          have hq1_ne : q₁ ≠ 0 := fun hq0 => by
            rw [hq0, zero_smul, sub_zero] at heq0
            have hr1_ne : r₁ ≠ 0 := fun hr0 => hpqr (by simp [hp0, hq0, hr0])
            exact hv_nz a.succ b.succ (fin_succ_ne (fun h => hab (congrArg cls h)))
              ((smul_eq_zero.mp heq0).resolve_left hr1_ne)
          have hr1_ne : r₁ ≠ 0 := fun hr0 => by
            rw [hr0, zero_smul, zero_sub, neg_eq_zero] at heq0
            exact hv_nz a'.succ b.succ (fin_succ_ne (fun h => hab (haa'.trans (congrArg cls h))))
              ((smul_eq_zero.mp heq0).resolve_left hq1_ne)
          refine ⟨r₁ / q₁, div_ne_zero hr1_ne hq1_ne, ?_⟩
          have heq1 : q₁ • v a'.succ b.succ = r₁ • v a.succ b.succ := (sub_eq_zero.mp heq0).symm
          calc v a'.succ b.succ = q₁⁻¹ • (q₁ • v a'.succ b.succ) := by
                rw [smul_smul, inv_mul_cancel₀ hq1_ne, one_smul]
            _ = (r₁ / q₁) • v a.succ b.succ := by rw [heq1, smul_smul, div_eq_inv_mul]
      have hcross_prop : ∀ {a a' b b' : Fin q}, cls a = cls a' → cls b = cls b' → cls a ≠ cls b →
          ∃ c : ℝ, c ≠ 0 ∧ v a'.succ b'.succ = c • v a.succ b.succ := fun {a a' b b'} ha hb hab => by
        obtain ⟨c₁, hc1, hstep1⟩ := hcross_step ha hab
        obtain ⟨c₂, hc2, hstep2⟩ := hcross_step hb (fun h => hab (ha.trans h.symm))
        refine ⟨c₁ * c₂, mul_ne_zero hc1 hc2, ?_⟩
        calc v a'.succ b'.succ = - v b'.succ a'.succ := hv_sym _ _
          _ = - (c₂ • v b.succ a'.succ) := by rw [hstep2]
          _ = c₂ • (- v b.succ a'.succ) := (smul_neg _ _).symm
          _ = c₂ • v a'.succ b.succ := by rw [← hv_sym b.succ a'.succ]
          _ = c₂ • (c₁ • v a.succ b.succ) := by rw [hstep1]
          _ = (c₁ * c₂) • v a.succ b.succ := by rw [smul_smul, mul_comm c₂ c₁]
      let vU : Fin (s + 1) → Fin (s + 1) → Ambient d := fun i j =>
        Fin.cases
          (Fin.cases 0 (fun r => v 0 (rep r).succ) j)
          (fun r₁ => Fin.cases (v (rep r₁).succ 0) (fun r₂ => v (rep r₁).succ (rep r₂).succ) j)
          i
      have hvU_rep : ∀ i j : Fin (s + 1),
          vU i j = v (Fin.cases 0 (fun r => (rep r).succ) i) (Fin.cases 0 (fun r => (rep r).succ) j) := by
        intro i j
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero =>
            simp only [vU, Fin.cases_zero]
            have hv00 : v 0 0 = 0 := by
              have h := hv_sym 0 0
              have : (2 : ℝ) • v 0 0 = 0 := by
                calc (2 : ℝ) • v 0 0 = v 0 0 + v 0 0 := two_smul ℝ _
                  _ = v 0 0 + (- v 0 0) := by conv_lhs => rhs; rw [h]
                  _ = 0 := add_neg_cancel _
              exact (smul_eq_zero.mp this).resolve_left two_ne_zero
            exact hv00.symm
          | succ r => simp only [vU, Fin.cases_zero, Fin.cases_succ]
        | succ r₁ =>
          induction j using Fin.cases with
          | zero => simp only [vU, Fin.cases_zero, Fin.cases_succ]
          | succ r₂ => simp only [vU, Fin.cases_succ]
      have hrep_inj : Function.Injective (Fin.cases (0 : Fin (q + 1)) (fun r => (rep r).succ)) := by
        intro x y h
        induction x using Fin.cases with
        | zero =>
          induction y using Fin.cases with
          | zero => rfl
          | succ r => simp only [Fin.cases_zero, Fin.cases_succ] at h; exact False.elim (Fin.succ_ne_zero _ h.symm)
        | succ r₁ =>
          induction y using Fin.cases with
          | zero => simp only [Fin.cases_zero, Fin.cases_succ] at h; exact False.elim (Fin.succ_ne_zero _ h)
          | succ r₂ =>
            simp only [Fin.cases_succ] at h
            have hrep_eq : rep r₁ = rep r₂ := Fin.succ_injective _ h
            rw [← hcls_rep r₁, ← hcls_rep r₂, hrep_eq]
      have hvU_sym : ∀ i j, vU j i = - vU i j := fun i j => by
        rw [hvU_rep, hvU_rep, hv_sym]
      have hvU_nz : ∀ i j, i ≠ j → vU i j ≠ 0 := fun i j hij => by
        rw [hvU_rep]
        exact hv_nz _ _ (fun h => hij (hrep_inj h))
      have hvU_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • vU i j + c₂ • vU j k + c₃ • vU k i = 0 :=
          fun i j k hij hjk hik => by
        rw [hvU_rep, hvU_rep, hvU_rep]
        exact hv_tri _ _ _ (fun h => hij (hrep_inj h)) (fun h => hjk (hrep_inj h)) (fun h => hik (hrep_inj h))
      have hvU_dim : s ≤ Module.finrank ℝ
          (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (s + 1), x = vU i j}) := by
        have hle : U ≤ Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (s + 1), x = vU i j} := by
          rw [hU_eq_rep]
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact Submodule.subset_span ⟨0, r.succ, rfl⟩
        exact hU_finrank.symm.le.trans (Submodule.finrank_mono hle)
      obtain ⟨shU₀, heqU₀, hvalU₀, θU₀, hθU₀⟩ := ih s hs_lt_q hs1 (by omega) (by omega) vU hvU_sym hvU_nz hvU_tri hvU_dim
      obtain ⟨shU, heqU, hvalU, θU, hθU⟩ := exists_liftShape (q - 1) (by omega) shU₀ hvalU₀
        (fun e => vU (Fin.cast (congrArg (· + 1) heqU₀) e.1.1) (Fin.cast (congrArg (· + 1) heqU₀) e.1.2))
        ⟨θU₀, fun e => hθU₀ e⟩
      have hshC_ex : ∀ r : Fin s, ∃ (shC : TreeShape d (q - 1))
          (heqC : shC.dim = (classSet q s cls r).card - 1),
          shC.Valid ∧
          ∃ θC : shC.ParamIdx → ℝ,
            ∀ e : Pairs (shC.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              shC.evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                         (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r => by
        let C := classSet q s cls r
        by_cases hC1 : C.card = 1
        · have hunit_dim : (TreeShape.unit (d := d)).dim = 0 := rfl
          obtain ⟨shC, heqC, hvalC, θC, _⟩ := exists_liftShape (q - 1) (Nat.zero_le _)
            (TreeShape.unit (d := d)) (by trivial)
            (fun _ => 0) ⟨Empty.elim, fun e => by
              exfalso
              have hle0 : (e.1.1 : ℕ) < (e.1.2 : ℕ) := e.2
              have hlt0 : (e.1.2 : ℕ) < (TreeShape.unit (d := d)).dim + 1 := e.1.2.2
              omega⟩
          have hdim0 : shC.dim = 0 := heqC.trans hunit_dim
          have hcard1 : (classSet q s cls r).card = 1 := hC1
          refine ⟨shC, by rw [hdim0, hcard1], hvalC, θC, fun e => ?_⟩
          exfalso
          have hle0 : (e.1.1 : ℕ) < (e.1.2 : ℕ) := e.2
          have hlt0 : (e.1.2 : ℕ) < shC.dim + 1 := e.1.2.2
          omega
        · have hC_ge1' : 1 ≤ (classSet q s cls r).card := hC_ge1 r
          have hC1' : (classSet q s cls r).card ≠ 1 := hC1
          have hC2 : 2 ≤ C.card := by
            change 2 ≤ (classSet q s cls r).card
            omega
          let q_r := C.card - 1
          have hqr1 : 1 ≤ q_r := by omega
          have hqr_lt : q_r < q := by
            have hle : C.card ≤ q := by simpa [C] using Finset.card_le_univ C
            omega
          have hC_card_eq : C.card = q_r + 1 := by omega
          let ord : Fin (q_r + 1) ≃o C := C.orderIsoOfFin hC_card_eq
          let v_r : Fin (q_r + 1) → Fin (q_r + 1) → Ambient d := fun i j => v (ord i).1.succ (ord j).1.succ
          have hv_r_sym : ∀ i j, v_r j i = - v_r i j := fun i j => hv_sym _ _
          have hv_r_nz : ∀ i j, i ≠ j → v_r i j ≠ 0 := fun i j hij =>
            hv_nz _ _ (fin_succ_ne (fun h => hij (ord.injective (Subtype.ext h))))
          have hv_r_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
              ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • v_r i j + c₂ • v_r j k + c₃ • v_r k i = 0 :=
              fun i j k hij hjk hik =>
            hv_tri _ _ _
              (fin_succ_ne (fun h => hij (ord.injective (Subtype.ext h))))
              (fin_succ_ne (fun h => hjk (ord.injective (Subtype.ext h))))
              (fin_succ_ne (fun h => hik (ord.injective (Subtype.ext h))))
          have hv_r_dim : q_r ≤ Module.finrank ℝ
              (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q_r + 1), x = v_r i j}) := by
            have hle : V r ≤ Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q_r + 1), x = v_r i j} := by
              refine Submodule.span_le.mpr ?_
              rintro _ ⟨a, ha, b, hb, _, rfl⟩
              exact Submodule.subset_span ⟨ord.symm ⟨a, ha⟩, ord.symm ⟨b, hb⟩, by simp [v_r]⟩
            exact (hV_finrank_eq r).symm.le.trans (Submodule.finrank_mono hle)
          obtain ⟨shC₀, heqC₀, hvalC₀, θC₀, hθC₀⟩ :=
            ih q_r hqr_lt hqr1 (by omega) (by omega) v_r hv_r_sym hv_r_nz hv_r_tri hv_r_dim
          obtain ⟨shC, heqC, hvalC, θC, hθC⟩ :=
            exists_liftShape (q - 1) (by omega) shC₀ hvalC₀
              (fun e => v_r (Fin.cast (congrArg (· + 1) heqC₀) e.1.1) (Fin.cast (congrArg (· + 1) heqC₀) e.1.2))
              ⟨θC₀, fun e => hθC₀ e⟩
          refine ⟨shC, heqC.trans heqC₀, hvalC, θC, fun e => ?_⟩
          obtain ⟨c, hc, hce⟩ := hθC e
          refine ⟨c, hc, ?_⟩
          rw [hce]
          have hcast1 : (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.1))).1 =
              (((classSet q s cls r).orderIsoOfFin rfl)
                (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.1)).1 :=
            orderIsoOfFin_val_eq (classSet q s cls r) hC_card_eq rfl _ _ rfl
          have hcast2 : (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.2))).1 =
              (((classSet q s cls r).orderIsoOfFin rfl)
                (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.2)).1 :=
            orderIsoOfFin_val_eq (classSet q s cls r) hC_card_eq rfl _ _ rfl
          change c • v (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.1))).1.succ
                       (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.2))).1.succ =
                 c • v (((classSet q s cls r).orderIsoOfFin rfl)
                         (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.1)).1.succ
                       (((classSet q s cls r).orderIsoOfFin rfl)
                         (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.2)).1.succ
          rw [hcast1, hcast2]
      let q' : Fin 6 := ⟨q, by omega⟩
      let s' : Fin 6 := ⟨s, by omega⟩
      let shC_fn : Fin s'.1 → TreeShape d (q - 1) := fun r => Classical.choose (hshC_ex r)
      have hshC_spec : ∀ r : Fin s, ∃ (heqC : (shC_fn r).dim = (classSet q s cls r).card - 1),
          (shC_fn r).Valid ∧
          ∃ θC : (shC_fn r).ParamIdx → ℝ,
            ∀ e : Pairs ((shC_fn r).dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              (shC_fn r).evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                               (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_ex r)
      let heqC_fn : ∀ r : Fin s, (shC_fn r).dim = (classSet q s cls r).card - 1 := fun r =>
        Classical.choose (hshC_spec r)
      have hshC_val : ∀ r : Fin s, (shC_fn r).Valid ∧
          ∃ θC : (shC_fn r).ParamIdx → ℝ,
            ∀ e : Pairs ((shC_fn r).dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              (shC_fn r).evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                               (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_spec r)
      let θC_fn : ∀ r : Fin s, (shC_fn r).ParamIdx → ℝ := fun r => Classical.choose (hshC_val r).2
      have hθC_fn : ∀ (r : Fin s) (e : Pairs ((shC_fn r).dim + 1)), ∃ c : ℝ, c ≠ 0 ∧
          let ord := (classSet q s cls r).orderIsoOfFin rfl
          (shC_fn r).evalEdges (θC_fn r) e = c • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                                 (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_val r).2
      let sh1 : TreeShape d ((q - 1) + 1) := .split q' s' cls shU shC_fn
      have hsh1_val : sh1.Valid := ⟨hq2, hqd, hs1, hs_lt_q, hC_ge1, hvalU, heqU.trans heqU₀,
        fun r => ⟨(hshC_val r).1, heqC_fn r⟩⟩
      let θ1 : (TreeShape.split q' s' cls shU shC_fn).ParamIdx → ℝ :=
        Sum.elim θU (fun p => θC_fn p.1 p.2)
      have hs_dim_eq : shU.dim = s := heqU.trans heqU₀
      have hs'_val : s'.1 = s := rfl
      have hU_dim_eq : s'.1 + 1 = shU.dim + 1 := by rw [hs_dim_eq, hs'_val]
      have hrep1_aux : ∀ (e : Pairs (q'.1 + 1)), ∃ c : ℝ, c ≠ 0 ∧
          (TreeShape.split q' s' cls shU shC_fn).evalEdges θ1 e = c • v e.1.1 e.1.2 := fun e => by
        rw [evalEdges_split]
        have hlt_e : e.1.1 < e.1.2 := e.2
        have hθU_eq : (fun x => θ1 (Sum.inl x)) = θU := rfl
        rcases Fin.eq_zero_or_eq_succ e.1.1 with hi | ⟨a, hi⟩
        · rcases Fin.eq_zero_or_eq_succ e.1.2 with hj | ⟨b, hj⟩
          · exact False.elim (Fin.ne_of_lt hlt_e (hi.trans hj.symm))
          · rw [hi, hj]
            simp only [Fin.cases_zero, Fin.cases_succ, hU_dim_eq, ↓reduceDIte, hθU_eq]
            obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
            have hspan : Submodule.span ℝ {w b} = Submodule.span ℝ {w (rep (cls b))} :=
              (hcls_iff b (rep (cls b))).mp (hcls_rep (cls b)).symm
            have hmem : w (rep (cls b)) ∈ Submodule.span ℝ {w b} := by
              rw [hspan]; exact Submodule.subset_span rfl
            obtain ⟨c₁, hc1⟩ := Submodule.mem_span_singleton.mp hmem
            have hc1_ne : c₁ ≠ 0 := fun h0 => by
              rw [h0, zero_smul] at hc1
              exact hv_nz 0 (rep (cls b)).succ (Fin.succ_ne_zero _).symm hc1.symm
            refine ⟨c₀ * c₁, mul_ne_zero hc0 hc1_ne, ?_⟩
            rw [hce0]
            have hc0_eq : Fin.cast (congrArg (· + 1) heqU₀)
                (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (0 : Fin (s'.1 + 1)))) =
                (0 : Fin (s + 1)) := Fin.ext rfl
            have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                (cls b).succ := Fin.ext rfl
            have hvU0 : vU (Fin.cast (congrArg (· + 1) heqU₀)
                  (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (0 : Fin (s'.1 + 1)))))
                (Fin.cast (congrArg (· + 1) heqU₀)
                  (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ))) =
                v 0 (rep (cls b)).succ := by
              rw [hvU_rep, hc0_eq, hcb_eq]; rfl
            dsimp [castPair] at hvU0 ⊢
            rw [hvU0]
            change c₀ • w (rep (cls b)) = (c₀ * c₁) • v 0 b.succ
            rw [← hc1]
            change c₀ • (c₁ • v 0 b.succ) = (c₀ * c₁) • v 0 b.succ
            rw [smul_smul]
        · rcases Fin.eq_zero_or_eq_succ e.1.2 with hj | ⟨b, hj⟩
          · rw [hi, hj] at hlt_e
            exact False.elim (Nat.not_lt_zero _ hlt_e)
          · have hab_lt : a < b := by
              have hlt' : (e.1.1 : ℕ) < (e.1.2 : ℕ) := hlt_e
              rw [hi, hj] at hlt'
              exact Nat.succ_lt_succ_iff.mp hlt'
            rw [hi, hj]
            simp only [Fin.cases_succ]
            by_cases hcls : cls a = cls b
            · simp only [dif_pos hcls]
              let r := cls a
              let C := classSet q'.1 s'.1 cls r
              have hC_ge1' : 1 ≤ (classSet q s cls r).card := hC_ge1 r
              have heqC' : (shC_fn r).dim = (classSet q s cls r).card - 1 := heqC_fn r
              have hC_eq : C.card = (shC_fn r).dim + 1 := by
                change (classSet q s cls r).card = (shC_fn r).dim + 1
                omega
              rw [dif_pos hC_eq]
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card := ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              have hij' : i' < j' := ord.symm.strictMono (Subtype.mk_lt_mk.mpr hab_lt)
              have hθC_eq : (fun x => θ1 (Sum.inr ⟨r, x⟩)) = θC_fn r := rfl
              rw [dif_pos hij', hθC_eq]
              obtain ⟨c₀, hc0, hce0⟩ := hθC_fn r (castPair hC_eq ⟨(i', j'), hij'⟩)
              refine ⟨c₀, hc0, ?_⟩
              rw [hce0]
              have hord_i : (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega)
                  (Fin.cast hC_eq i'))).1 = a := by
                have hfi : Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq i') = i' := by
                  ext; rfl
                rw [hfi]
                change (ord (ord.symm ⟨a, _⟩)).1 = a
                simp
              have hord_j : (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega)
                  (Fin.cast hC_eq j'))).1 = b := by
                have hfj : Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq j') = j' := by
                  ext; rfl
                rw [hfj]
                change (ord (ord.symm ⟨b, _⟩)).1 = b
                simp
              dsimp [castPair]
              change c₀ • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq i'))).1.succ
                           (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq j'))).1.succ =
                     c₀ • v a.succ b.succ
              rw [hord_i, hord_j]
            · simp only [dif_neg hcls, dif_pos hU_dim_eq, hθU_eq]
              rcases lt_or_gt_of_ne hcls with hlt | hgt
              · simp only [dif_pos hlt]
                obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
                obtain ⟨c₃, hc3, hce3⟩ := hcross_prop (hcls_rep (cls a)).symm (hcls_rep (cls b)).symm hcls
                refine ⟨c₀ * c₃, mul_ne_zero hc0 hc3, ?_⟩
                rw [hce0]
                have hca_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)) =
                    (cls a).succ := Fin.ext rfl
                have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                    (cls b).succ := Fin.ext rfl
                have hvU_e : vU (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)))
                    (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ))) =
                    v (rep (cls a)).succ (rep (cls b)).succ := by
                  rw [hvU_rep, hca_eq, hcb_eq]; rfl
                dsimp [castPair] at hvU_e ⊢
                rw [hvU_e, hce3, smul_smul]
              · have hnot : ¬ cls a < cls b := Nat.not_lt.mpr hgt.le
                simp only [dif_neg hnot, dif_pos hgt]
                obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
                obtain ⟨c₃, hc3, hce3⟩ := hcross_prop (hcls_rep (cls a)).symm (hcls_rep (cls b)).symm hcls
                refine ⟨c₀ * c₃, mul_ne_zero hc0 hc3, ?_⟩
                rw [hce0]
                have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                    (cls b).succ := Fin.ext rfl
                have hca_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)) =
                    (cls a).succ := Fin.ext rfl
                have hvU_e : vU (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)))
                    (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ))) =
                    v (rep (cls b)).succ (rep (cls a)).succ := by
                  rw [hvU_rep, hcb_eq, hca_eq]; rfl
                dsimp [castPair] at hvU_e ⊢
                rw [hvU_e, hv_sym (rep (cls a)).succ (rep (cls b)).succ, smul_neg, neg_neg, hce3, smul_smul]
      have hrep1 : ∀ e : Pairs (sh1.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
          sh1.evalEdges θ1 e = c • v e.1.1 e.1.2 := hrep1_aux
      obtain ⟨sh, heq, hval, θ, hθ⟩ := exists_liftShape q (by omega) sh1 hsh1_val
        (fun e => v e.1.1 e.1.2) ⟨θ1, hrep1⟩
      refine ⟨sh, heq, hval, θ, fun e => ?_⟩
      exact hθ e

private structure MaxRankConfig (d m : ℕ) where
  sh : {sh : TreeShape d 5 // sh.Valid ∧ sh.dim = 5}
  σ : Fin m → Pairs6
  piv : Fin m → Fin d

private instance instFiniteMaxRankConfig (d m : ℕ) : Finite (MaxRankConfig d m) :=
  Finite.of_injective
    (fun c : MaxRankConfig d m => (c.sh, c.σ, c.piv))
    (fun c₁ c₂ h => by
      cases c₁; cases c₂
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl)

private abbrev MaxRankParamIdx (d m : ℕ) (c : MaxRankConfig d m) : Type :=
  c.sh.1.ParamIdx ⊕ ((a : Fin m) × {j : Fin d // j ≠ c.piv a})

private lemma card_maxRankParamIdx {d m : ℕ} (c : MaxRankConfig d m) :
    Fintype.card (MaxRankParamIdx d m c) ≤ 5 * d - 1 + m * (d - 1) := by
  have h1 : Fintype.card c.sh.1.ParamIdx ≤ 5 * d - 1 := by
    have hb := card_paramIdx_bound c.sh.1 c.sh.2.1
    rwa [c.sh.2.2] at hb
  have h2 : ∀ a : Fin m, Fintype.card {j : Fin d // j ≠ c.piv a} = d - 1 := fun a => by
    have heq : {j : Fin d // j ≠ c.piv a} ≃
        {j : Fin d // j ∈ Finset.univ.erase (c.piv a)} :=
      Equiv.subtypeEquivRight fun j => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  simp only [MaxRankParamIdx, Fintype.card_sum, Fintype.card_sigma, h2, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_le_add_right h1 (m * (d - 1))

private noncomputable def coordCLM {d : ℕ} (j : Fin d) : Ambient d →L[ℝ] ℝ :=
  { toFun := fun x => x j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    cont := (continuous_apply j).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous }

private noncomputable def maxRankNormal {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) (a : Fin m) : Ambient d :=
  c.sh.1.evalEdges (fun idx => y (Sum.inl idx))
    (castPair (congrArg (· + 1) c.sh.2.2.symm) (c.σ a))

private def maxRankP0 {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.piv a then 0 else y (Sum.inr ⟨a, ⟨j, h⟩⟩)

private noncomputable def maxRankOpen {d m : ℕ} (c : MaxRankConfig d m) :
    Set (MaxRankParamIdx d m c → ℝ) :=
  {y | ∀ a : Fin m, maxRankNormal c y a (c.piv a) ≠ 0}

private noncomputable def maxRankMap {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) : Fin (m * d) → ℝ :=
  fun x =>
    let p := finProdFinEquiv.symm x
    if p.2 = c.piv p.1 then
      - (∑ j : Fin d, maxRankNormal c y p.1 j * maxRankP0 c y p.1 j) /
          maxRankNormal c y p.1 (c.piv p.1)
    else
      maxRankP0 c y p.1 p.2

private lemma differentiableOn_maxRankMap {d m : ℕ} (c : MaxRankConfig d m) :
    DifferentiableOn ℝ (maxRankMap c) (maxRankOpen c) := by
  have hθ : Differentiable ℝ (fun y : MaxRankParamIdx d m c → ℝ => fun idx => y (Sum.inl idx)) :=
    differentiable_pi.mpr fun idx => differentiable_apply (Sum.inl idx)
  have hn : ∀ a j, Differentiable ℝ fun y => maxRankNormal c y a j := fun a j =>
    (coordCLM j).differentiable.comp
      ((differentiable_evalEdges c.sh.1 _).comp hθ)
  have hp0 : ∀ a j, Differentiable ℝ fun y => maxRankP0 c y a j := fun a j => by
    dsimp [maxRankP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiableOn_pi.mpr fun x => ?_
  dsimp [maxRankMap]
  split_ifs
  · simp_rw [div_eq_mul_inv]
    exact ((Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg.differentiableOn).mul
      (((hn _ _).differentiableOn).inv fun y (hy : y ∈ maxRankOpen c) => hy _)
  · exact (hp0 _ _).differentiableOn

private lemma mem_range_maxRankMap_of_tree {d m : ℕ}
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j)
    (hS_univ : nonEmptyIntParts C = Finset.univ)
    (hnne : ∀ i j : Fin 6, i ≠ j → n i j ≠ 0)
    (hnsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hno_int : ∀ (k₁ : Fin 6) (a : Fin m), evalPoints z a ∉ interior (C k₁ : Set (Ambient d)))
    (sh : TreeShape d 5) (hsh_val : sh.Valid) (hsh_dim : sh.dim = 5)
    (θ : sh.ParamIdx → ℝ)
    (hθ : ∀ e : Pairs (sh.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
      sh.evalEdges θ e =
        c • n (Fin.cast (congrArg (· + 1) hsh_dim) e.1.1)
              (Fin.cast (congrArg (· + 1) hsh_dim) e.1.2)) :
    ∃ c : MaxRankConfig d m, z ∈ maxRankMap c '' maxRankOpen c := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  have hex_sig : ∀ a : Fin m, ∃ e : Pairs6, ⟪n e.1.1 e.1.2, p a⟫_ℝ = 0 := fun a => by
    obtain ⟨i, _hiS, j, _hjS, hij, hzero⟩ :=
      skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
        (fun q hq => hno_int q a hq)
    exact ⟨⟨(i, j), hij⟩, hzero⟩
  choose σ hσ_zero using hex_sig
  have hex_piv : ∀ a : Fin m, ∃ j : Fin d,
      sh.evalEdges θ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)) j ≠ 0 := fun a => by
    obtain ⟨c₀, hc0, hce0⟩ := hθ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a))
    have hcast1 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.1 = (σ a).1.1 := Fin.ext rfl
    have hcast2 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.2 = (σ a).1.2 := Fin.ext rfl
    rw [hcast1, hcast2] at hce0
    have hne0 : sh.evalEdges θ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)) ≠ 0 := by
      rw [hce0]
      exact smul_ne_zero hc0 (hnne _ _ (Fin.ne_of_lt (σ a).2))
    by_contra hall
    push Not at hall
    exact hne0 (PiLp.ext hall)
  choose piv hpiv_ne using hex_piv
  let cfg : MaxRankConfig d m := ⟨⟨sh, hsh_val, hsh_dim⟩, σ, piv⟩
  let y : MaxRankParamIdx d m cfg → ℝ :=
    Sum.elim θ (fun q => p q.1 q.2.1)
  have hy_open : y ∈ maxRankOpen cfg := fun a => by
    dsimp [maxRankNormal, cfg]
    exact hpiv_ne a
  have hy_N_perp : ∀ a : Fin m, ∑ j : Fin d, maxRankNormal cfg y a j * p a j = 0 := fun a => by
    obtain ⟨c₀, _, hce0⟩ := hθ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a))
    have hcast1 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.1 = (σ a).1.1 := Fin.ext rfl
    have hcast2 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.2 = (σ a).1.2 := Fin.ext rfl
    rw [hcast1, hcast2] at hce0
    have hinner0 : ⟪maxRankNormal cfg y a, p a⟫_ℝ = 0 := by
      have heq_θ : (fun idx => y (Sum.inl idx)) = θ := rfl
      dsimp [maxRankNormal, cfg]
      rw [heq_θ, hce0, real_inner_smul_left, hσ_zero a, mul_zero]
    simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
      conj_trivial, mul_comm] using hinner0
  refine ⟨cfg, y, hy_open, ?_⟩
  funext x
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [maxRankMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = cfg.piv a := hj
    have hp0_eq : ∀ q : Fin d, maxRankP0 cfg y a q =
        if q = cfg.piv a then 0 else p a q := fun q => by
      dsimp [maxRankP0, cfg, y]
    simp_rw [hp0_eq]
    have hsplit : ∑ q : Fin d, maxRankNormal cfg y a q * (if q = cfg.piv a then 0 else p a q) =
        ∑ q ∈ Finset.univ.erase (cfg.piv a), maxRankNormal cfg y a q * p a q := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (cfg.piv a))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [(Finset.mem_erase.mp hq).1]
    have hsplit_full : ∑ q : Fin d, maxRankNormal cfg y a q * p a q =
        maxRankNormal cfg y a (cfg.piv a) * p a (cfg.piv a) +
          ∑ q ∈ Finset.univ.erase (cfg.piv a), maxRankNormal cfg y a q * p a q :=
      (Finset.add_sum_erase Finset.univ (fun q => maxRankNormal cfg y a q * p a q)
        (Finset.mem_univ (cfg.piv a))).symm
    rw [hy_N_perp a] at hsplit_full
    have hpiv0 : maxRankNormal cfg y a (cfg.piv a) ≠ 0 := hy_open a
    have hpj : p a (cfg.piv a) = z (finProdFinEquiv (a, j)) := by
      rw [← hj_eq, hp_eq]
    rw [hsplit, ← hpj]
    exact div_eq_of_eq_mul hpiv0 (by rw [mul_comm]; linarith)
  · have hj_ne : j ≠ cfg.piv a := hj
    dsimp [maxRankP0, y]
    split_ifs with h
    · exact False.elim (hj_ne h)
    · exact hp_eq

/-- Unconditional existence of `5 * d` central blocking points in `unitBall d` (`d ≥ 30`). -/
theorem exists_isBlocking_5d (d : ℕ) (hd : 30 ≤ d) :
    ∃ p : Fin (5 * d) → Ambient d, IsBlocking p := by
  let m := 5 * d
  have hmd : 0 < m * d := by positivity
  have hm_prod : m * d = m * (d - 1) + m := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    ring
  let badA : Set (Fin (m * d) → ℝ) := ⋃ c : RrefConfig d m 4, Set.range (rrefParamMap c)
  have hbadA_vol : (volume : Measure (Fin (m * d) → ℝ)) badA = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (RrefParamIdx c.I.1 c.rDom c.σ) < m * d := by
      rw [card_rrefParamIdx c, hm_prod]
      dsimp [m]
      omega
    exact volume_range_eq_zero_of_card_lt hmd hcard (differentiable_rrefParamMap c)
  let badB : Set (Fin (m * d) → ℝ) := ⋃ c : MaxRankConfig d m, maxRankMap c '' maxRankOpen c
  have hbadB_vol : (volume : Measure (Fin (m * d) → ℝ)) badB = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (MaxRankParamIdx d m c) < m * d := by
      have hle := card_maxRankParamIdx c
      rw [hm_prod]
      dsimp [m] at hle ⊢
      omega
    exact volume_image_eq_zero_of_card_lt hmd hcard (differentiableOn_maxRankMap c)
  let bad : Set (Fin (m * d) → ℝ) := badA ∪ badB
  have hbad_vol : (volume : Measure (Fin (m * d) → ℝ)) bad = 0 := by
    rw [measure_union_null hbadA_vol hbadB_vol]
  let good : Set (Fin (m * d) → ℝ) :=
    {z | ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1}
  have hgood_open : IsOpen good := by
    have heq : good = ⋂ a : Fin m, (fun z => evalPoints z a) ⁻¹' Metric.ball (0 : Ambient d) 1 := by
      ext z; simp [good]
    rw [heq]
    refine isOpen_iInter_of_finite fun a => Metric.isOpen_ball.preimage ?_
    exact (continuous_apply a).comp continuous_evalPoints
  have hzero_good : (0 : Fin (m * d) → ℝ) ∈ good := fun a => by
    have hev : evalPoints (0 : Fin (m * d) → ℝ) a = 0 := by
      apply PiLp.ext
      intro j
      rfl
    rw [hev]
    exact Metric.mem_ball_self zero_lt_one
  have hgood_pos : 0 < (volume : Measure (Fin (m * d) → ℝ)) good :=
    hgood_open.measure_pos volume ⟨0, hzero_good⟩
  have hnot_sub : ¬ good ⊆ bad := fun hsub => by
    have hle : (volume : Measure (Fin (m * d) → ℝ)) good ≤ volume bad := measure_mono hsub
    rw [hbad_vol] at hle
    exact (lt_of_lt_of_le hgood_pos hle).ne' rfl
  obtain ⟨z, hz_good, hz_not_bad⟩ := Set.not_subset.mp hnot_sub
  refine ⟨evalPoints z, ?_⟩
  by_contra hnot_block
  dsimp [IsBlocking] at hnot_block
  push Not at hnot_block
  obtain ⟨C, hcov, hdisj, h0, hno_int⟩ := hnot_block
  obtain ⟨n, _hnii, hnsym, hnnotS, hsep⟩ := exists_central_separating_normals C hdisj h0
  by_cases hindep : LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)
  · obtain ⟨hS_univ, htri⟩ := rank5_triangle_dependent C hcov n hnnotS
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.1,
        (hsep i hi j hj hij).2.2.2.1, (hsep i hi j hj hij).2.2.2.2⟩)
      hnsym hindep
    have hnz : ∀ i j : Fin 6, i ≠ j → n i j ≠ 0 := fun i j hij =>
      (hsep i (hS_univ ▸ Finset.mem_univ i) j (hS_univ ▸ Finset.mem_univ j) hij).1
    have htri' : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
        ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • n i j + c₂ • n j k + c₃ • n k i = 0 :=
        fun i j k hij hjk hik => by
      obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := htri i j k hij hjk hik
      refine ⟨c₁, c₂, c₃, ?_, hcomb⟩
      intro heq0
      rcases hne with h | h | h
      · exact h (congrArg Prod.fst heq0)
      · exact h (congrArg (fun p => p.2.1) heq0)
      · exact h (congrArg (fun p => p.2.2) heq0)
    have hdim : 5 ≤ Module.finrank ℝ
        (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin 6, x = n i j}) := by
      have hle : Submodule.span ℝ (Set.range fun t : Fin 5 => ∑ j : Fin 6, n t.succ j) ≤
          Submodule.span ℝ {x : Ambient d | ∃ i j : Fin 6, x = n i j} := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨t, rfl⟩
        exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨t.succ, j, rfl⟩
      have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) = 5 := by
        have h := (linearIndependent_iff_card_eq_finrank_span.mp hindep).symm
        simpa [Set.finrank, Fintype.card_fin] using h
      exact hcard.symm.le.trans (Submodule.finrank_mono hle)
    obtain ⟨sh, hsh_dim, hsh_val, θ, hθ⟩ :=
      exists_treeParam 5 (by norm_num) le_rfl (by omega) n hnsym hnz htri' hdim
    obtain ⟨c, hc⟩ := mem_range_maxRankMap_of_tree z hz_good C hcov n hnsym hS_univ hnz
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.2.1⟩)
      hno_int sh hsh_val hsh_dim θ hθ
    exact hz_not_bad (Or.inr (Set.mem_iUnion.mpr ⟨c, hc⟩))
  · obtain ⟨I, u, hI_inj, hu_rref, hcoef⟩ := separating_normals_in_rref4_span (by omega : 4 ≤ d)
      C hcov n hnnotS (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.1⟩)
      hnsym hindep
    obtain ⟨c, hc⟩ := mem_range_rrefParamMap_of_span (by norm_num : 1 ≤ 4) z hz_good C hcov n
      hnsym (fun i hi j hj hij => (hsep i hi j hj hij).1)
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.2.1⟩)
      hno_int I u hI_inj hu_rref hcoef
    exact hz_not_bad (Or.inl (Set.mem_iUnion.mpr ⟨c, hc⟩))

private theorem convex_partition_from_base {d₀ d : ℕ} (hd₀ : 2 ≤ d₀) (hd : d₀ ≤ d)
    {g₀ : (Fin (5 * d₀) → ℝ) → (Fin (d₀ - 2) → ℝ)} (hg₀ : IsAlmostSixEmbedding g₀)
    {p : Fin (5 * d) → Ambient d} (hp : IsBlocking p) :
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

/-- **`d ≥ 24` reduction with `5 * d - 4` central blocking markers**: pads Theorem A
`d - 8` times to `Δ^(5d-5) → ℝ^(d-2)` and transfers any central blocking set `p` via
Blaschke compactness (`exists_eta_of_isBlocking`) and `inwardDist`. -/
theorem convex_partition_counterexample_ge_24 (d : ℕ) (hd : 24 ≤ d)
    (p : Fin (5 * d - 4) → Ambient d) (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg₀⟩ := tverberg_counterexample
  obtain ⟨g₁, hg₁⟩ := iterated_padding_from (d - 8) hg₀
  obtain ⟨g, hg⟩ := reindex_almostSixEmbedding (by omega : 36 + 5 * (d - 8) = 5 * d - 4)
    (by omega : 6 + (d - 8) = d - 2) hg₁
  exact convex_partition_of_embedding_and_blocking (by omega) hg hp

/-- **Conditional `d ≥ 18` reduction (Section 3.1–3.3 of the research report)**: in every
dimension `d ≥ 18`, given an almost six-embedding `g₀ : Δ⁸⁹ → ℝ¹⁶` and `5 * d` central
blocking markers `p`, Blaschke compactness, join-padding `d - 18` times, and inward-distance
transfer yield the same obstruction. -/
theorem convex_partition_counterexample_ge_18 (d : ℕ) (hd : 18 ≤ d)
    (g₀ : (Fin 90 → ℝ) → (Fin 16 → ℝ)) (hg₀ : IsAlmostSixEmbedding g₀)
    (p : Fin (5 * d) → Ambient d) (hp : IsBlocking p) :
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
central blocking markers suffice without any external almost-six-embedding assumption. -/
theorem convex_partition_counterexample_ge_36 (d : ℕ) (hd : 36 ≤ d)
    (p : Fin (5 * d) → Ambient d) (hp : IsBlocking p) :
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

/-- **Theorem B (completely unconditional, `d ≥ 36`)**: In every dimension `d ≥ 36`,
obtains `5 * d` central blocking markers unconditionally via `exists_isBlocking_5d`
(combining rank-4 RREF reduction and full rank-5 tree parametrization via
`exists_treeParam`), constructs an unconditional almost six-embedding `Δ^(5d-1) → ℝ^(d-2)`
from the fivefold join of Theorem A (`fivefold_tverberg_join`) plus join-padding, and
produces `d - 1` continuous functionals on convex bodies and an absolutely continuous
probability measure without equalizing convex six-partitions. -/
theorem convex_partition_counterexample (d : ℕ) (hd : 36 ≤ d) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨p, hp⟩ := exists_isBlocking_5d d (by omega)
  exact convex_partition_counterexample_ge_36 d hd p hp

end AkopyanSixfold
end
