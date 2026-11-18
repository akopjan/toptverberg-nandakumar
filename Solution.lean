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

private abbrev Pairs6 := {e : Fin 6 × Fin 6 // e.1 < e.2}

private lemma card_pairs6 : Fintype.card Pairs6 = 15 := by decide

private abbrev ParamIdx {d m : ℕ}
    (I : Fin 5 → Fin d) (rDom : Pairs6 → Fin 5) (σ : Fin m → Pairs6) :=
  (Fin 5 × {j : Fin d // ∀ r, I r ≠ j}) ⊕
  ((e : Pairs6) × {r : Fin 5 // r ≠ rDom e}) ⊕
  ((a : Fin m) × {j : Fin d // j ≠ I (rDom (σ a))})

private structure DiscreteConfig (d m : ℕ) where
  I : {I : Fin 5 → Fin d // Function.Injective I}
  rDom : Pairs6 → Fin 5
  σ : Fin m → Pairs6

private instance (d m : ℕ) : Finite (DiscreteConfig d m) :=
  Finite.of_injective
    (fun c : DiscreteConfig d m => (c.I, c.rDom, c.σ))
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

private def paramU {d m : ℕ} (c : DiscreteConfig d m)
    (y : ParamIdx c.I.1 c.rDom c.σ → ℝ) (r : Fin 5) (j : Fin d) : ℝ :=
  if _h : c.I.1 r = j then 1
  else if h' : ∃ s : Fin 5, c.I.1 s = j then 0
  else y (Sum.inl (r, ⟨j, fun s hs => h' ⟨s, hs⟩⟩))

private def paramC {d m : ℕ} (c : DiscreteConfig d m)
    (y : ParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (r : Fin 5) : ℝ :=
  if h : r = c.rDom e then 1
  else y (Sum.inr (Sum.inl ⟨e, ⟨r, h⟩⟩))

private def paramN {d m : ℕ} (c : DiscreteConfig d m)
    (y : ParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (j : Fin d) : ℝ :=
  ∑ r : Fin 5, paramC c y e r * paramU c y r j

private def paramP0 {d m : ℕ} (c : DiscreteConfig d m)
    (y : ParamIdx c.I.1 c.rDom c.σ → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.I.1 (c.rDom (c.σ a)) then 0
  else y (Sum.inr (Sum.inr ⟨a, ⟨j, h⟩⟩))

private def paramMap {d m : ℕ} (c : DiscreteConfig d m)
    (y : ParamIdx c.I.1 c.rDom c.σ → ℝ) : Fin (m * d) → ℝ :=
  fun k =>
    let p := finProdFinEquiv.symm k
    if p.2 = c.I.1 (c.rDom (c.σ p.1)) then
      - ∑ j : Fin d, paramN c y (c.σ p.1) j * paramP0 c y p.1 j
    else
      paramP0 c y p.1 p.2

private lemma differentiable_paramMap {d m : ℕ} (c : DiscreteConfig d m) :
    Differentiable ℝ (paramMap c) := by
  have hu : ∀ r j, Differentiable ℝ fun y => paramU c y r j := fun r j => by
    dsimp [paramU]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_const 0
    · exact differentiable_apply _
  have hc : ∀ e r, Differentiable ℝ fun y => paramC c y e r := fun e r => by
    dsimp [paramC]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_apply _
  have hn : ∀ e j, Differentiable ℝ fun y => paramN c y e j := fun e j =>
    Differentiable.fun_sum fun r _ => (hc e r).mul (hu r j)
  have hp0 : ∀ a j, Differentiable ℝ fun y => paramP0 c y a j := fun a j => by
    dsimp [paramP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiable_pi.mpr fun k => ?_
  dsimp [paramMap]
  split_ifs
  · exact (Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg
  · exact hp0 _ _

private lemma card_paramIdx_lt {d : ℕ} (hd : 5 ≤ d) (c : DiscreteConfig d (5 * d + 36)) :
    Fintype.card (ParamIdx c.I.1 c.rDom c.σ) < (5 * d + 36) * d := by
  let m := 5 * d + 36
  have h1 : Fintype.card {j : Fin d // ∀ r : Fin 5, c.I.1 r ≠ j} = d - 5 := by
    let sRest : Finset (Fin d) := Finset.univ \ Finset.univ.image c.I.1
    have heq : {j : Fin d // ∀ r : Fin 5, c.I.1 r ≠ j} ≃ {j : Fin d // j ∈ sRest} :=
      Equiv.subtypeEquivRight fun j => by
        simp [sRest, Finset.mem_sdiff, Finset.mem_image]
    rw [Fintype.card_congr heq, Fintype.card_coe]
    have hsub : Finset.univ.image c.I.1 ⊆ (Finset.univ : Finset (Fin d)) :=
      Finset.subset_univ _
    dsimp [sRest]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ c.I.2, Finset.card_univ, Fintype.card_fin]
  have h2 : ∀ e : Pairs6, Fintype.card {r : Fin 5 // r ≠ c.rDom e} = 4 := fun e => by
    have heq : {r : Fin 5 // r ≠ c.rDom e} ≃
        {r : Fin 5 // r ∈ Finset.univ.erase (c.rDom e)} :=
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
  have hcard :
      Fintype.card (ParamIdx c.I.1 c.rDom c.σ) = 5 * (d - 5) + 15 * 4 + m * (d - 1) := by
    simp only [ParamIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_fin, h1, h2, h3, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      card_pairs6]
    ring
  rw [hcard]
  have hm_prod : m * d = m * (d - 1) + m := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    ring
  rw [hm_prod]
  set A := m * (d - 1)
  change 5 * (d - 5) + 15 * 4 + A < A + (5 * d + 36)
  omega

private lemma volume_range_eq_zero_of_card_lt {N : ℕ} (hN : 0 < N)
    {γ : Type*} [Fintype γ] (hcard : Fintype.card γ < N)
    {Ψ : (γ → ℝ) → (Fin N → ℝ)} (hΨ : Differentiable ℝ Ψ) :
    (volume : Measure (Fin N → ℝ)) (Set.range Ψ) = 0 := by
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
  have hsub : Set.range Ψ ⊆ (Ψ ∘ L) '' (H₀ : Set (Fin N → ℝ)) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨M y, hM_mem y, ?_⟩
    simp [Function.comp_apply, hLM y]
  have himg_zero : (volume : Measure (Fin N → ℝ)) ((Ψ ∘ L) '' (H₀ : Set (Fin N → ℝ))) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (volume : Measure (Fin N → ℝ)) (hΨ.comp hL_diff).differentiableOn hH₀_vol
  exact measure_mono_null hsub himg_zero

private lemma mem_range_paramMap_of_not_blocking {d m : ℕ} (hd : 5 ≤ d)
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (hnot_block : ¬ IsBlocking (evalPoints z)) :
    ∃ c : DiscreteConfig d m, z ∈ Set.range (paramMap c) := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  dsimp [IsBlocking] at hnot_block
  push Not at hnot_block
  obtain ⟨C, hcov, hdisj, h0, hno_int⟩ := hnot_block
  let S := nonEmptyIntParts C
  obtain ⟨n, I, u, hI_inj, hu_rref, _hnii, hnsym, _hnnotS, hnne, hnsep, hcoef⟩ :=
    separating_normals_in_rref_span hd C hcov hdisj h0
  have hex_rDom : ∀ e : Pairs6, ∃ r : Fin 5,
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
        have hsum0 : (∑ r : Fin 5, n e.1.1 e.1.2 (I r) * u r j) = 0 :=
          Finset.sum_eq_zero fun r _ => by rw [(hall r).2.2, zero_mul]
        exact hsum0
      exact hne0 hzero
    · refine ⟨0, fun h1 h2 => False.elim (hmem ⟨h1, h2⟩)⟩
  choose rDom hrDom_spec using hex_rDom
  have hex_sig : ∀ a : Fin m,
      ∃ e : Pairs6, e.1.1 ∈ S ∧ e.1.2 ∈ S ∧ ⟪n e.1.1 e.1.2, p a⟫_ℝ = 0 := by
    intro a
    obtain ⟨i, hiS, j, hjS, hij, hzero⟩ :=
      skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
        (fun k hk => hno_int k a hk)
    exact ⟨⟨(i, j), hij⟩, hiS, hjS, hzero⟩
  choose σ hσ1 hσ2 hσ_zero using hex_sig
  let cfg : DiscreteConfig d m := ⟨⟨I, hI_inj⟩, rDom, σ⟩
  let cCoef : Pairs6 → Fin 5 → ℝ := fun e r =>
    if e.1.1 ∈ S ∧ e.1.2 ∈ S then
      (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r)
    else if r = rDom e then 1 else 0
  have hc_dom : ∀ e : Pairs6, cCoef e (rDom e) = 1 := fun e => by
    dsimp [cCoef]
    by_cases h : e.1.1 ∈ S ∧ e.1.2 ∈ S
    · simp [h, inv_mul_cancel₀ (hrDom_spec e h.1 h.2)]
    · simp [h]
  let y : ParamIdx cfg.I.1 cfg.rDom cfg.σ → ℝ
    | Sum.inl (r, j) => u r j.1
    | Sum.inr (Sum.inl ⟨e, r⟩) => cCoef e r.1
    | Sum.inr (Sum.inr ⟨a, j⟩) => p a j.1
  have hy_U : ∀ r j, paramU cfg y r j = u r j := fun r j => by
    dsimp [paramU, cfg]
    split_ifs with h1 h2
    · rw [← h1, hu_rref r r]; simp
    · obtain ⟨s, hs⟩ := h2
      have hrs : r ≠ s := fun h => h1 (h ▸ hs)
      rw [← hs, hu_rref r s]; simp [hrs]
    · rfl
  have hy_C : ∀ e r, paramC cfg y e r = cCoef e r := fun e r => by
    dsimp [paramC, cfg]
    split_ifs with h
    · rw [h, hc_dom e]
    · rfl
  have hy_N_perp : ∀ a : Fin m, ∑ j : Fin d, paramN cfg y (σ a) j * p a j = 0 := fun a => by
    let e := σ a
    have h1 : e.1.1 ∈ S := hσ1 a
    have h2 : e.1.2 ∈ S := hσ2 a
    have hN_eq : ∀ j : Fin d, paramN cfg y e j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 j := fun j => by
      dsimp [paramN]
      have hc_eq : ∀ r : Fin 5, paramC cfg y e r =
          (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r) := fun r => by
        rw [hy_C e r]
        dsimp [cCoef]
        simp only [h1, h2, and_self, ↓reduceIte]
      simp_rw [hc_eq, hy_U]
      rw [hcoef e.1.1 e.1.2 j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hN_mul : ∀ j : Fin d, paramN cfg y (σ a) j * p a j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * (n e.1.1 e.1.2 j * p a j) := fun j => by
      rw [show σ a = e from rfl, hN_eq j, mul_assoc]
    simp_rw [hN_mul]
    rw [← Finset.mul_sum]
    have hdot : ∑ j : Fin d, n e.1.1 e.1.2 j * p a j = 0 := by
      simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
        conj_trivial, mul_comm] using hσ_zero a
    rw [hdot, mul_zero]
  have hy_N_piv : ∀ e : Pairs6, paramN cfg y e (I (rDom e)) = 1 := fun e => by
    dsimp [paramN]
    simp_rw [hy_C, hy_U, hu_rref]
    rw [Finset.sum_eq_single (rDom e)]
    · simp [hc_dom e]
    · intro r _ hr; simp [hr]
    · intro hr; exact False.elim (hr (Finset.mem_univ _))
  refine ⟨cfg, y, ?_⟩
  funext k
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [paramMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = I (rDom (σ a)) := hj
    have hp0_eq : ∀ k : Fin d, paramP0 cfg y a k =
        if k = I (rDom (σ a)) then 0 else p a k := fun k => by
      dsimp [paramP0, cfg]
      split_ifs <;> rfl
    simp_rw [hp0_eq]
    have hsplit : ∑ k : Fin d, paramN cfg y (σ a) k * (if k = I (rDom (σ a)) then 0 else p a k) =
        (∑ k ∈ Finset.univ.erase (I (rDom (σ a))), paramN cfg y (σ a) k * p a k) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (I (rDom (σ a))))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [(Finset.mem_erase.mp hk).1]
    have hsplit_full : ∑ k : Fin d, paramN cfg y (σ a) k * p a k =
        paramN cfg y (σ a) (I (rDom (σ a))) * p a (I (rDom (σ a))) +
          ∑ k ∈ Finset.univ.erase (I (rDom (σ a))), paramN cfg y (σ a) k * p a k :=
      (Finset.add_sum_erase Finset.univ (fun k => paramN cfg y (σ a) k * p a k)
        (Finset.mem_univ (I (rDom (σ a))))).symm
    rw [hy_N_perp a, hy_N_piv (σ a), one_mul] at hsplit_full
    have hpj : p a (I (rDom (σ a))) = p a j := by rw [← hj_eq]
    change - ∑ k : Fin d, paramN cfg y (σ a) k * (if k = I (rDom (σ a)) then 0 else p a k) =
      z (finProdFinEquiv (a, j))
    rw [hsplit]
    linarith [hsplit_full, hpj, hp_eq]
  · have hj_ne : j ≠ I (rDom (σ a)) := hj
    dsimp [paramP0, cfg, y]
    simp [hj_ne, hp_eq]

/-- Unconditional existence of `5 * d + 36` central blocking points in `unitBall d` (`d ≥ 5`). -/
theorem exists_isBlocking (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : Fin (5 * d + 36) → Ambient d, IsBlocking p := by
  let m := 5 * d + 36
  have hmd : 0 < m * d := by positivity
  let bad : Set (Fin (m * d) → ℝ) := ⋃ c : DiscreteConfig d m, Set.range (paramMap c)
  have hbad_vol : (volume : Measure (Fin (m * d) → ℝ)) bad = 0 := by
    refine measure_iUnion_null fun c => ?_
    exact volume_range_eq_zero_of_card_lt hmd (card_paramIdx_lt hd c) (differentiable_paramMap c)
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
  obtain ⟨c, hc⟩ := mem_range_paramMap_of_not_blocking hd z hz_good hnot_block
  exact hz_not_bad (Set.mem_iUnion.mpr ⟨c, hc⟩)

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

/-- **Theorem B (completely unconditional, `d ≥ 288`)**: In every dimension `d ≥ 288`,
obtains `5 * d + 36` central blocking markers unconditionally via `exists_isBlocking`,
derives `eta` via Blaschke compactness (`exists_eta_of_isBlocking`), constructs an
unconditional almost six-embedding `Δ^(5d+35) → ℝ^(d-2)` (`padded_tverberg_ge_288`), and
produces `d - 1` continuous functionals on convex bodies and an absolutely continuous
probability measure without equalizing convex six-partitions. -/
theorem convex_partition_counterexample (d : ℕ) (hd : 288 ≤ d) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g, hg⟩ := padded_tverberg_ge_288 d hd
  obtain ⟨p, hp⟩ := exists_isBlocking d (by omega)
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

end AkopyanSixfold
end
