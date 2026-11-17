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
  In every dimension `d ≥ 24`, given `5 * d - 4` blocking markers for `eta`-central
  six-partitions, iterates join-padding (`d - 8` times) from Theorem A to produce an
  almost six-embedding `g : Δ^(5d-5) → ℝ^(d-2)`, transfers it via the Hausdorff-continuous
  inward-distance functional `inwardDist` to `d - 1` continuous body functionals `Phi`,
  and proves that no fair convex six-partition equalizes `Phi` for any `eta`-concentrated
  absolutely continuous measure (nor for a normalized Lebesgue ball restriction).
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

/-- A marker tuple `p : Fin m → Ambient d` and radius `eta ∈ (0, 1)` block
`eta`-central convex six-partitions of the unit ball if every convex six-partition
whose parts all meet the closed `eta`-ball contains at least one marker `p a`
in the interior of some part `C i` (Lemmas 5.1–5.2 of the manuscript). -/
def IsCentralBlocking {d m : ℕ} (p : Fin m → Ambient d) (eta : ℝ) : Prop :=
  0 < eta ∧ eta < 1 ∧
  ∀ C : Fin 6 → Body d,
    IsSixPartition C →
    (∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty) →
    ∃ i a, p a ∈ interior (C i : Set (Ambient d))

/-! ### Helper 1: Join-padding of almost six-embeddings (Lemma 3.3) -/

private lemma padMap_headSum_nonneg {n : ℕ} {x : Fin (n + 5) → ℝ}
    (hx : x ∈ simplex (n + 5)) :
    0 ≤ ∑ v : Fin n, x (Fin.castAdd 5 v) :=
  Finset.sum_nonneg fun _ _ => hx.1 _

private lemma padMap_proj_mem_simplex {n : ℕ} (hn : 0 < n)
    {x : Fin (n + 5) → ℝ} (hx : x ∈ simplex (n + 5)) :
    (let t := ∑ v : Fin n, x (Fin.castAdd 5 v)
     if t = 0 then Pi.single ⟨0, hn⟩ (1 : ℝ) else fun v => x (Fin.castAdd 5 v) / t) ∈
      simplex n := by
  dsimp only
  set t := ∑ v : Fin n, x (Fin.castAdd 5 v)
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    refine ⟨fun v => ?_, by simp⟩
    by_cases hv : v = ⟨0, hn⟩ <;> simp [hv]
  · simp only [ht, ↓reduceIte]
    have ht_nonneg : 0 ≤ t := padMap_headSum_nonneg hx
    refine ⟨fun v => div_nonneg (hx.1 _) ht_nonneg, ?_⟩
    rw [← Finset.sum_div]
    exact div_self ht

/-- Join-padding preserves almost six-embeddings (adding 5 vertices and 1 target coordinate). -/
private lemma padding_almostSixEmbedding {n q : ℕ} (hn : 0 < n)
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : IsAlmostSixEmbedding g) :
    ∃ f : (Fin (n + 5) → ℝ) → (Fin (q + 1) → ℝ),
      IsAlmostSixEmbedding f := by
  let t : (Fin (n + 5) → ℝ) → ℝ := fun x => ∑ v : Fin n, x (Fin.castAdd 5 v)
  let yProj : (Fin (n + 5) → ℝ) → Fin n → ℝ := fun x =>
    if t x = 0 then Pi.single ⟨0, hn⟩ (1 : ℝ) else fun v => x (Fin.castAdd 5 v) / t x
  let f : (Fin (n + 5) → ℝ) → (Fin (q + 1) → ℝ) := fun x =>
    Fin.cons (t x) (fun j => t x * g (yProj x) j)
  have ht_cont : Continuous t :=
    continuous_finsetSum _ fun v _ => continuous_apply (Fin.castAdd 5 v)
  have hcompact : IsCompact (simplex n) := isCompact_stdSimplex ℝ (Fin n)
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hg.1
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hbound : ∀ y ∈ simplex n, ∀ j : Fin q, |g y j| ≤ M := by
    intro y hy j
    have h1 : |g y j| ≤ ‖g y‖ := norm_le_pi_norm (g y) j
    exact h1.trans ((hM₀ y hy).trans (le_max_left M₀ 0))
  refine ⟨f, ?_, ?_⟩
  · refine continuousOn_pi.mpr fun k => Fin.cases ?_ ?_ k
    · simpa [f] using ht_cont.continuousOn
    · intro j x hx
      by_cases htx : t x = 0
      · have hfx0 : f x j.succ = 0 := by simp [f, htx]
        change Filter.Tendsto (fun u => t u * g (yProj u) j)
          (𝓝[simplex (n + 5)] x) (𝓝 (f x j.succ))
        rw [hfx0]
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        refine squeeze_zero' (g := fun u => M * |t u|)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with u hu
          change ‖t u * g (yProj u) j‖ ≤ M * |t u|
          rw [Real.norm_eq_abs, abs_mul]
          by_cases htu : t u = 0
          · simp [htu]
          · have hyu : yProj u ∈ simplex n := padMap_proj_mem_simplex hn hu
            have hle : |g (yProj u) j| ≤ M := hbound _ hyu j
            calc
              |t u| * |g (yProj u) j| ≤ |t u| * M := by gcongr
              _ = M * |t u| := mul_comm _ _
        · have htend : Filter.Tendsto (fun u => M * |t u|)
              (𝓝[simplex (n + 5)] x) (𝓝 (M * |t x|)) :=
            ((continuous_const.mul (ht_cont.abs)).continuousWithinAt).tendsto
          simpa [htx] using htend
      · let yRaw : (Fin (n + 5) → ℝ) → Fin n → ℝ :=
          fun u v => u (Fin.castAdd 5 v) / t u
        have hyRaw_cont : ContinuousAt yRaw x := by
          refine continuousAt_pi.mpr fun v => ?_
          exact (continuous_apply _).continuousAt.div ht_cont.continuousAt htx
        have hnhds : {u | t u ≠ 0} ∈ 𝓝 x :=
          ht_cont.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds htx)
        have h_maps : Filter.Tendsto yRaw (𝓝[simplex (n + 5)] x) (𝓝[simplex n] (yRaw x)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨hyRaw_cont.continuousWithinAt, ?_⟩
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnhds] with u hu htu
          have hyu : yProj u ∈ simplex n := padMap_proj_mem_simplex hn hu
          simpa [yProj, htu, yRaw] using hyu
        have hx_in : yRaw x ∈ simplex n := by
          have hyx : yProj x ∈ simplex n := padMap_proj_mem_simplex hn hx
          simpa [yProj, htx, yRaw] using hyx
        have hg_at : ContinuousWithinAt (fun y => g y j) (simplex n) (yRaw x) :=
          (continuous_apply j).continuousAt.comp_continuousWithinAt (hg.1 (yRaw x) hx_in)
        have hcomp : ContinuousWithinAt (fun u => t u * g (yRaw u) j) (simplex (n + 5)) x :=
          ht_cont.continuousWithinAt.mul (hg_at.tendsto.comp h_maps)
        refine hcomp.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [nhdsWithin_le_nhds hnhds] with u htu
          simp [f, yProj, htu, yRaw]
        · simp [f, yProj, htx, yRaw]
  · intro x hx hdisj
    by_contra h_all
    push Not at h_all
    have ht_eq : ∀ i, t (x i) = t (x 0) := fun i => by
      have h0 := congrFun (h_all i) 0
      simpa [f] using h0
    by_cases ht0 : t (x 0) = 0
    · have hw_sum : ∀ i, (∑ w : Fin 5, x i (Fin.natAdd n w)) = 1 := fun i => by
        have hsum := (hx i).2
        rw [Fin.sum_univ_add] at hsum
        have hhead : t (x i) = 0 := (ht_eq i).trans ht0
        change t (x i) + ∑ w : Fin 5, x i (Fin.natAdd n w) = 1 at hsum
        linarith
      have hex_w : ∀ i, ∃ w : Fin 5, x i (Fin.natAdd n w) ≠ 0 := fun i => by
        by_contra hzero
        push Not at hzero
        have hsum0 : (∑ w : Fin 5, x i (Fin.natAdd n w)) = 0 :=
          Finset.sum_eq_zero fun w _ => hzero w
        linarith [hw_sum i]
      choose w hw using hex_w
      obtain ⟨i, j, hij, hwij⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt w (by simp)
      rcases hdisj i j hij (Fin.natAdd n (w i)) with hi0 | hj0
      · exact hw i hi0
      · rw [hwij] at hj0
        exact hw j hj0
    · have hti : ∀ i, t (x i) ≠ 0 := fun i => (ht_eq i).symm ▸ ht0
      have hy_mem : ∀ i, yProj (x i) ∈ simplex n :=
        fun i => padMap_proj_mem_simplex hn (hx i)
      have hy_disj : DisjointSupports (fun i => yProj (x i)) := by
        intro i j hij v
        rcases hdisj i j hij (Fin.castAdd 5 v) with hi0 | hj0
        · left; simp [yProj, hti i, hi0]
        · right; simp [yProj, hti j, hj0]
      obtain ⟨i, hi_ne⟩ := hg.2 (fun i => yProj (x i)) hy_mem hy_disj
      apply hi_ne
      funext j
      have hj_eq := congrFun (h_all i) j.succ
      simp only [f, Fin.cons_succ] at hj_eq
      rw [ht_eq i] at hj_eq
      exact mul_left_cancel₀ ht0 hj_eq

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

private lemma iterated_padding (k : ℕ) :
    ∃ f : (Fin (36 + 5 * k) → ℝ) → (Fin (6 + k) → ℝ),
      IsAlmostSixEmbedding f := by
  induction k with
  | zero =>
    simpa using tverberg_counterexample
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨f, hf⟩ := padding_almostSixEmbedding (by omega : 0 < 36 + 5 * k) hg
    exact reindex_almostSixEmbedding (by omega : 36 + 5 * k + 5 = 36 + 5 * (k + 1))
      (by omega : 6 + k + 1 = 6 + (k + 1)) hf

private lemma padded_almostSixEmbedding {d : ℕ} (hd : 24 ≤ d) :
    ∃ g : (Fin (5 * d - 4) → ℝ) → (Fin (d - 2) → ℝ),
      IsAlmostSixEmbedding g := by
  obtain ⟨g, hg⟩ := iterated_padding (d - 8)
  exact reindex_almostSixEmbedding (by omega : 36 + 5 * (d - 8) = 5 * d - 4)
    (by omega : 6 + (d - 8) = d - 2) hg

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

/-- **Theorem B (Conditional on central blocking markers)**:
For every dimension `d ≥ 24` and every `eta`-central blocking tuple `p` of
`5 * d - 4` markers, there exist `d - 1` continuous functionals `Phi` on convex
bodies (chosen before the measure) that cannot be equalized on any fair convex
six-partition of the unit ball for any `eta`-concentrated absolutely continuous
measure `mu`, and in particular for a concrete absolutely continuous probability
measure on `Ambient d`. -/
theorem convex_partition_counterexample :
    ∀ d : ℕ, 24 ≤ d →
    ∀ (p : Fin (5 * d - 4) → Ambient d) (eta : ℝ),
      IsCentralBlocking p eta →
      ∃ Phi : Body d → (Fin (d - 1) → ℝ),
        Continuous Phi ∧
        (∀ mu : Measure (Ambient d),
          mu.AbsolutelyContinuous (volume : Measure (Ambient d)) →
          0 < mu (unitBall d) →
          mu (unitBall d) < ⊤ →
          5 * mu (unitBall d) <
            6 * mu (Metric.closedBall (0 : Ambient d) eta) →
          ∀ C : Fin 6 → Body d,
            IsSixPartition C →
            (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
            ∃ i, Phi (C i) ≠ Phi (C 0)) ∧
        (∃ mu : Measure (Ambient d),
          IsProbabilityMeasure mu ∧
          mu.AbsolutelyContinuous (volume : Measure (Ambient d)) ∧
          ∀ C : Fin 6 → Body d,
            IsSixPartition C →
            (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
            ∃ i, Phi (C i) ≠ Phi (C 0)) := by
  intro d hd p eta hp
  have hd_pos : 0 < d := by omega
  obtain ⟨g, hg⟩ := padded_almostSixEmbedding hd
  have hcompact : IsCompact (simplex (5 * d - 4)) := isCompact_stdSimplex ℝ (Fin (5 * d - 4))
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hg.1
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hbound : ∀ y ∈ simplex (5 * d - 4), ∀ j : Fin (d - 2), |g y j| ≤ M := by
    intro y hy j
    exact (norm_le_pi_norm (g y) j).trans ((hM₀ y hy).trans (le_max_left M₀ 0))
  let w : Body d → Fin (5 * d - 4) → ℝ := fun C a => inwardDist (p a) C
  let s : Body d → ℝ := fun C => ∑ a, w C a
  let Phi : Body d → (Fin (d - 1) → ℝ) := fun C k =>
    if hk : k.1 = 0 then s C
    else
      if s C = 0 then 0
      else s C * g (fun a => w C a / s C) ⟨k.1 - 1, by omega⟩
  have hw_nonneg : ∀ C a, 0 ≤ w C a := fun _ _ => Metric.infDist_nonneg
  have hs_nonneg : ∀ C, 0 ≤ s C := fun C => Finset.sum_nonneg fun a _ => hw_nonneg C a
  have hs_cont : Continuous s := continuous_finsetSum _ fun a _ => continuous_inwardDist hd_pos (p a)
  have h_simplex_of_pos : ∀ C, s C ≠ 0 → (fun a => w C a / s C) ∈ simplex (5 * d - 4) := by
    intro C hsC
    refine ⟨fun a => div_nonneg (hw_nonneg C a) (hs_nonneg C), ?_⟩
    rw [← Finset.sum_div]
    exact div_self hsC
  have hPhi_cont : Continuous Phi := by
    refine continuous_pi fun k => ?_
    by_cases hk : k.1 = 0
    · simpa [Phi, hk] using hs_cont
    · have hfun :
          (fun C : Body d => Phi C k) =
            fun C => if s C = 0 then 0 else s C * g (fun a => w C a / s C) ⟨k.1 - 1, by omega⟩ :=
        funext fun C => by simp [Phi, hk]
      rw [hfun]
      refine continuous_iff_continuousAt.mpr fun C₀ => ?_
      by_cases hs₀ : s C₀ = 0
      · change Filter.Tendsto (fun C : Body d =>
          if s C = 0 then (0 : ℝ)
          else s C * g (fun a => w C a / s C) ⟨k.1 - 1, by omega⟩) (𝓝 C₀) (𝓝 _)
        dsimp only
        simp only [hs₀, ↓reduceIte]
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        refine squeeze_zero' (g := fun C => M * s C)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (Filter.Eventually.of_forall fun C => ?_) ?_
        · by_cases hsC : s C = 0
          · simp [hsC, M, hM_nonneg, hs_nonneg C]
          · simp only [hsC, ↓reduceIte, Real.norm_eq_abs, abs_mul]
            have hyC : (fun a => w C a / s C) ∈ simplex (5 * d - 4) :=
              h_simplex_of_pos C hsC
            have hle := hbound _ hyC ⟨k.1 - 1, by omega⟩
            calc
              |s C| * |g (fun a => w C a / s C) ⟨k.1 - 1, by omega⟩|
                ≤ |s C| * M := by gcongr
              _ = M * |s C| := mul_comm _ _
              _ = M * s C := by rw [abs_of_nonneg (hs_nonneg C)]
        · have htend : Filter.Tendsto (fun C : Body d => M * s C) (𝓝 C₀) (𝓝 (M * s C₀)) :=
            (continuous_const.mul hs_cont).continuousAt.tendsto
          simpa [hs₀] using htend
      · let yMap : Body d → Fin (5 * d - 4) → ℝ := fun C a => w C a / s C
        have hyMap_cont : ContinuousAt yMap C₀ := by
          refine continuousAt_pi.mpr fun a => ?_
          exact ((continuous_inwardDist hd_pos (p a)).continuousAt).div
            hs_cont.continuousAt hs₀
        have hnhds : {C : Body d | s C ≠ 0} ∈ 𝓝 C₀ :=
          hs_cont.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hs₀)
        have h_maps : Filter.Tendsto yMap (𝓝 C₀) (𝓝[simplex (5 * d - 4)] (yMap C₀)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨hyMap_cont.tendsto, ?_⟩
          filter_upwards [hnhds] with C hC
          exact h_simplex_of_pos C hC
        have hg_at : ContinuousWithinAt (fun y => g y ⟨k.1 - 1, by omega⟩)
            (simplex (5 * d - 4)) (yMap C₀) :=
          (continuous_apply _).continuousAt.comp_continuousWithinAt
            (hg.1 (yMap C₀) (h_simplex_of_pos C₀ hs₀))
        have h_prod : ContinuousAt (fun C : Body d => s C * g (yMap C) ⟨k.1 - 1, by omega⟩) C₀ :=
          hs_cont.continuousAt.mul (hg_at.tendsto.comp h_maps)
        refine h_prod.congr ?_
        filter_upwards [hnhds] with C hC
        simp [hC, yMap]
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
      obtain ⟨i, a, ha⟩ := hp.2.2 C hC hmeet
      exact hno_int i a ha
    · have hsi_ne : ∀ i, s (C i) ≠ 0 := fun i => (hs_eq i).symm ▸ hs0
      let x : Fin 6 → Fin (5 * d - 4) → ℝ := fun i a => w (C i) a / s (C i)
      have hx_mem : ∀ i, x i ∈ simplex (5 * d - 4) :=
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
      let k : Fin (d - 1) := ⟨j.1 + 1, by omega⟩
      have hk0 : k.1 ≠ 0 := by simp [k]
      have hcon := congrFun (h_all i) k
      simp only [Phi, hk0, ↓reduceDIte, hs_eq i, hs0, ↓reduceIte, k] at hcon
      have hksub : (⟨j.1 + 1 - 1, by omega⟩ : Fin (d - 2)) = j := by
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
  refine ⟨Phi, hPhi_cont, h_unif, ?_⟩
  exact ⟨_, hprob, hac, fun C hC hfair => h_unif _ hac hpos htop hconc C hC hfair⟩

end AkopyanSixfold
end
