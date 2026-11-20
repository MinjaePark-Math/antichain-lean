import Antichain.EmpiricalTopology
import Antichain.EmpiricalConcentration
import Antichain.CubeShiftSupport
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Finite positive continuous tests detecting holes and antichain outliers,
with explicit transport to the paper's native Euclidean Hausdorff metric. -/

noncomputable section

namespace Antichain

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction

def shapeBump {d : ℕ} (y : CubePoint d) (r : ℝ) : CubePoint d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (r - dist x y) 0, (continuous_const.sub (continuous_id.dist continuous_const)).max continuous_const⟩
    (max r 0) (by
      intro x z
      have hx0 : 0 ≤ max (r - dist x y) 0 := le_max_right _ _
      have hz0 : 0 ≤ max (r - dist z y) 0 := le_max_right _ _
      have hxu : max (r - dist x y) 0 ≤ max r 0 :=
        max_le_max (sub_le_self _ dist_nonneg) le_rfl
      have hzu : max (r - dist z y) 0 ≤ max r 0 :=
        max_le_max (sub_le_self _ dist_nonneg) le_rfl
      rw [Real.dist_eq]
      change |max (r - dist x y) 0 - max (r - dist z y) 0| ≤ max r 0
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

@[simp] theorem shapeBump_apply {d : ℕ} (y x : CubePoint d) (r : ℝ) :
    shapeBump y r x = max (r - dist x y) 0 := rfl

theorem shapeBump_nonneg {d : ℕ} (y x : CubePoint d) (r : ℝ) : 0 ≤ shapeBump y r x :=
  le_max_right _ _

theorem shapeBump_pos_iff {d : ℕ} (y x : CubePoint d) (r : ℝ) :
    0 < shapeBump y r x ↔ dist x y < r := by
  simp only [shapeBump_apply, lt_max_iff, lt_self_iff_false, or_false, sub_pos]

theorem shapeBump_integral_pos {d : ℕ} (mu : Measure (CubePoint d)) [IsFiniteMeasure mu]
    {y : CubePoint d} (hy : y ∈ mu.support) {r : ℝ} (hr : 0 < r) :
    0 < ∫ x, shapeBump y r x ∂mu := by
  apply (integral_pos_iff_support_of_nonneg (fun x => shapeBump_nonneg y x r)
    ((shapeBump y r).integrable (μ := mu))).mpr
  have hball : 0 < mu (ball y r) :=
    (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hr)
  apply hball.trans_le (measure_mono ?_)
  intro x hx
  exact ne_of_gt ((shapeBump_pos_iff y x r).mpr hx)

theorem cubePointSet_isCompact (d : ℕ) : IsCompact (cubePointSet d) := by
  convert (isCompact_pi_infinite (fun _ : Fin d => isCompact_Icc (a := (0 : ℝ)) (b := 1))) using 1
  ext x
  simp [cubePointSet, Pi.le_def, forall_and]

theorem limitingSupport_subset_cube {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    (limitingAntichainMeasure (Fin d)).support ⊆ cubePointSet d := by
  rw [limitingAntichainMeasure_support (by simpa using hd)]
  apply closure_minimal ?_ (cubePointSet_isCompact d).isClosed
  rintro x ⟨u, _, rfl⟩ i _
  exact ⟨(normalCDF_mem_Ioo (u i)).1.le, (normalCDF_mem_Ioo (u i)).2.le⟩

theorem limitingSupport_isCompact {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    IsCompact (limitingAntichainMeasure (Fin d)).support :=
  (cubePointSet_isCompact d).of_isClosed_subset (Measure.isClosed_support (μ := limitingAntichainMeasure (Fin d)))
    (limitingSupport_subset_cube hd)

theorem limitingSupport_nonempty (d : ℕ) : (limitingAntichainMeasure (Fin d)).support.Nonempty :=
  Measure.nonempty_support (by exact NeZero.ne _)

theorem isOpen_strictlyComparable (d : ℕ) :
    IsOpen {p : CubePoint d × CubePoint d | StrictBelow p.1 p.2 ∨ StrictBelow p.2 p.1} := by
  have hbelow : IsOpen {p : CubePoint d × CubePoint d | StrictBelow p.1 p.2} := by
    unfold StrictBelow
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd))
  have habove : IsOpen {p : CubePoint d × CubePoint d | StrictBelow p.2 p.1} := by
    unfold StrictBelow
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      ((continuous_apply i).comp continuous_snd) ((continuous_apply i).comp continuous_fst))
  exact hbelow.union habove

/-- Strict comparability persists for both arguments in fixed neighborhoods. -/
theorem comparable_neighborhoods {d : ℕ} (x y : CubePoint d)
    (hxy : StrictBelow x y ∨ StrictBelow y x) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ ball x r, ∀ v ∈ ball y r,
      StrictBelow u v ∨ StrictBelow v u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_strictlyComparable d) (x, y) hxy
  refine ⟨r, hr, fun u hu v hv => ?_⟩
  have hp : (u, v) ∈ ball (x, y) r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hu hv
  exact hball hp

theorem antichain_not_comparable {n d : ℕ} [NeZero d] (x : CubeSample n d)
    (hx : IsAntichain x) (j k : Fin n) : ¬ (StrictBelow (x j) (x k) ∨ StrictBelow (x k) (x j)) := by
  intro h
  by_cases hjk : j = k
  · subst k
    rcases h with h | h
    · exact lt_irrefl _ (h 0)
    · exact lt_irrefl _ (h 0)
  · rcases h with h | h
    · exact hx j k hjk h
    · exact hx k j (Ne.symm hjk) h

theorem finite_hole_tests {d : ℕ} [NeZero d] (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∃ I : Finset (CubePoint d →ᵇ ℝ),
      (∀ g ∈ I, (∀ x, 0 ≤ g x) ∧ 0 < ∫ x, g x ∂limitingAntichainMeasure (Fin d)) ∧
      ∀ n (x : CubeSample n d),
        (∀ g ∈ I, ∃ j, 0 < g (x j)) →
        ∀ y ∈ (limitingAntichainMeasure (Fin d)).support, ∃ j, dist y (x j) < r := by
  classical
  let S := (limitingAntichainMeasure (Fin d)).support
  have hcover : S ⊆ ⋃ y : S, ball y.val (r / 2) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by simp [hr]⟩
  obtain ⟨centers, hcenters⟩ := (limitingSupport_isCompact hd).elim_finite_subcover
    (fun y : S => ball y.val (r / 2)) (fun _ => isOpen_ball) hcover
  let I := centers.image (fun y => shapeBump y.val (r / 2))
  refine ⟨I, ?_, ?_⟩
  · intro g hg
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨fun x => shapeBump_nonneg _ _ _, shapeBump_integral_pos _ y.property (half_pos hr)⟩
  · intro n x hx y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcenters hy)
    obtain ⟨j, hj⟩ := hx (shapeBump z.val (r / 2)) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    refine ⟨j, ?_⟩
    have hdist := (shapeBump_pos_iff z.val (x j) (r / 2)).mp hj
    have htri := dist_triangle y z.val (x j)
    rw [dist_comm z.val (x j)] at htri
    change dist y z.val < r / 2 at hyz
    linarith

theorem finite_outlier_tests {d : ℕ} [NeZero d] (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∃ I : Finset (CubePoint d →ᵇ ℝ),
      (∀ g ∈ I, (∀ x, 0 ≤ g x) ∧ 0 < ∫ x, g x ∂limitingAntichainMeasure (Fin d)) ∧
      ∀ n (x : CubeSample n d), (∀ j, x j ∈ cubePointSet d) → IsAntichain x →
        (∀ g ∈ I, ∃ j, 0 < g (x j)) →
        ∀ j, infDist (x j) (limitingAntichainMeasure (Fin d)).support < r := by
  classical
  let S := (limitingAntichainMeasure (Fin d)).support
  let K : Set (CubePoint d) := {x | x ∈ cubePointSet d ∧ r ≤ infDist x S}
  have hK : IsCompact K := (cubePointSet_isCompact d).inter_right
    (isClosed_le continuous_const (continuous_infDist_pt S))
  have hlocal : ∀ x : K, ∃ y : CubePoint d, ∃ s : ℝ,
      y ∈ S ∧ 0 < s ∧ ∀ u ∈ ball x.val s, ∀ v ∈ ball y s,
        StrictBelow u v ∨ StrictBelow v u := by
    intro x
    have hnot : x.val ∉ S := by
      intro hx
      have hh := x.property.2
      rw [infDist_zero_of_mem hx] at hh
      linarith
    have hnot' : x.val ∉ closure (normalQuantileSurface (Fin d)) := by
      rwa [← (limitingAntichainMeasure_support_cubeShift_source (by simpa using hd)).1]
    obtain ⟨y, hy, hcomp⟩ := normalQuantile_cube_outside_closure_exists_comparable_cubeShift x.val
      (fun i => x.property.1 i (mem_univ i)) hnot'
    obtain ⟨s, hs, hcompare⟩ := comparable_neighborhoods x.val y hcomp
    have hys : y ∈ S := by
      change y ∈ (limitingAntichainMeasure (Fin d)).support
      rw [(limitingAntichainMeasure_support_cubeShift_source (by simpa using hd)).1]
      exact subset_closure hy
    exact ⟨y, s, hys, hs, hcompare⟩
  choose y s hys hs hcompare using hlocal
  have hcover : K ⊆ ⋃ x : K, ball x.val (s x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa only [mem_ball, dist_self] using hs ⟨x, hx⟩⟩
  obtain ⟨centers, hcenters⟩ := hK.elim_finite_subcover
    (fun x : K => ball x.val (s x)) (fun _ => isOpen_ball) hcover
  let I := centers.image (fun x => shapeBump (y x) (s x))
  refine ⟨I, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨fun z => shapeBump_nonneg _ _ _, shapeBump_integral_pos _ (hys x) (hs x)⟩
  · intro n x hcube hanti htests j
    by_contra hn
    have hxK : x j ∈ K := ⟨hcube j, not_lt.mp hn⟩
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcenters hxK)
    obtain ⟨k, hk⟩ := htests (shapeBump (y z) (s z)) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hky : x k ∈ ball (y z) (s z) := (shapeBump_pos_iff _ _ _).mp hk
    exact antichain_not_comparable x hanti j k (hcompare z _ hxz _ hky)

/-- Explicit metric bridge: the native Euclidean distance is at most √d
times the Pi-space sup distance. The final shape statement uses Euclidean
Hausdorff distance, exactly as in the manuscript. -/
theorem cube_euclidean_dist_le (d : ℕ) (x y : CubePoint d) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) ≤
      Real.sqrt (d : ℝ) * dist x y := by
  have hsum : ∑ i : Fin d, ‖(x - y) i‖ ^ 2 ≤ (d : ℝ) * ‖x - y‖ ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin d, ‖x - y‖ ^ 2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm (x - y) i))
      _ = _ := by simp
  have hsq : ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
      (Real.sqrt (d : ℝ) * ‖x - y‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [PiLp.toLp_apply, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hsum
  have hnonneg : 0 ≤ Real.sqrt (d : ℝ) * ‖x - y‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, ← WithLp.toLp_sub]
  nlinarith [norm_nonneg (WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d))]

def euclideanSampleSet (n d : ℕ) (x : CubeSample n d) : Set (EuclideanSpace ℝ (Fin d)) :=
  Set.range (fun j => WithLp.toLp 2 (x j))

def euclideanLimitingSupport (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp 2 '' (limitingAntichainMeasure (Fin d)).support

/-- The actual finite test family promised in the proof of Theorem 1.2.
Positive empirical values of every test exclude every hole and outlier,
and control the native Euclidean Hausdorff distance. -/
theorem finite_euclidean_shape_tests {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ I : Finset (CubePoint d →ᵇ ℝ),
      (∀ g ∈ I, (∀ x, 0 ≤ g x) ∧ 0 < ∫ x, g x ∂limitingAntichainMeasure (Fin d)) ∧
      ∀ n (x : CubeSample n d), (∀ j, x j ∈ cubePointSet d) → IsAntichain x →
        (∀ g ∈ I, ∃ j, 0 < g (x j)) →
        hausdorffDist (euclideanSampleSet n d x) (euclideanLimitingSupport d) ≤ δ := by
  classical
  have hdp : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdp
  let r := δ / Real.sqrt (d : ℝ)
  have hr : 0 < r := div_pos hδ hsqrt
  obtain ⟨holes, hholespos, hholes⟩ := finite_hole_tests hd hr
  obtain ⟨outliers, houtpos, houtliers⟩ := finite_outlier_tests hd hr
  refine ⟨holes ∪ outliers, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hholespos g hg
    · exact houtpos g hg
  · intro n x hcube hanti htests
    have hhole := hholes n x (fun g hg => htests g (Finset.mem_union_left _ hg))
    have hout := houtliers n x hcube hanti (fun g hg => htests g (Finset.mem_union_right _ hg))
    have hconvert {u v : CubePoint d} (huv : dist u v < r) :
        dist (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 v) ≤ δ := by
      have hle := (cube_euclidean_dist_le d u v).trans
        (mul_le_mul_of_nonneg_left huv.le hsqrt.le)
      simpa only [r, mul_div_cancel₀ _ hsqrt.ne'] using hle
    apply hausdorffDist_le_of_mem_dist hδ.le
    · rintro _ ⟨j, rfl⟩
      obtain ⟨y, hy, heq⟩ := (limitingSupport_isCompact hd).exists_infDist_eq_dist
        (limitingSupport_nonempty d) (x j)
      refine ⟨WithLp.toLp 2 y, ⟨y, hy, rfl⟩, hconvert ?_⟩
      rw [← heq]
      exact hout j
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := hhole y hy
      exact ⟨WithLp.toLp 2 (x j), ⟨j, rfl⟩, hconvert hj⟩

theorem positive_empirical_integral_exists {n d : ℕ} (hn : 0 < n) (x : CubeSample n d)
    (g : CubePoint d →ᵇ ℝ)
    (hg : 0 < ∫ u, g u ∂(empiricalCubeProbability n d x : Measure (CubePoint d))) :
    ∃ j, 0 < g (x j) := by
  classical
  rw [empiricalCubeProbability_integral n d hn x g] at hg
  by_contra hnexists
  have hall : ∀ j, g (x j) ≤ 0 := by simpa only [not_exists, not_lt] using hnexists
  have hsum := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hall j)
  have hdiv := div_nonpos_of_nonpos_of_nonneg hsum (Nat.cast_nonneg n)
  exact not_lt_of_ge hdiv hg

/-- A fixed actual open weak neighborhood controls the Euclidean Hausdorff
shape of every antichain, independently of sample size. -/
theorem euclidean_shape_weak_neighborhood {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set (ProbabilityMeasure (CubePoint d)), IsOpen U ∧ limitingCubeProbability d ∈ U ∧
      ∀ n, 0 < n → ∀ x : CubeSample n d, (∀ j, x j ∈ cubePointSet d) → IsAntichain x →
        empiricalCubeProbability n d x ∈ U →
        hausdorffDist (euclideanSampleSet n d x) (euclideanLimitingSupport d) ≤ δ := by
  classical
  obtain ⟨I, hIpos, hIdetect⟩ := finite_euclidean_shape_tests hd hδ
  let U : Set (ProbabilityMeasure (CubePoint d)) :=
    {nu | ∀ g ∈ I, (∫ x, g x ∂limitingAntichainMeasure (Fin d)) / 2 < ∫ x, g x ∂nu}
  have hUopen : IsOpen U := by
    dsimp only [U]
    simp only [setOf_forall]
    exact isOpen_biInter_finset (fun g _ => isOpen_lt continuous_const
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g))
  have hUmem : limitingCubeProbability d ∈ U := by
    intro g hg
    change (∫ x, g x ∂limitingAntichainMeasure (Fin d)) / 2 <
      ∫ x, g x ∂limitingAntichainMeasure (Fin d)
    linarith [(hIpos g hg).2]
  refine ⟨U, hUopen, hUmem, ?_⟩
  intro n hn x hcube hanti hx
  apply hIdetect n x hcube hanti
  intro g hg
  apply positive_empirical_integral_exists hn x g
  exact lt_trans (half_pos (hIpos g hg).2) (hx g hg)

theorem euclideanLimitingSupport_eq_closure_surface {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    euclideanLimitingSupport d =
      closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) '' normalQuantileSurface (Fin d)) := by
  rw [euclideanLimitingSupport,
    (limitingAntichainMeasure_support_cubeShift_source (by simpa using hd)).1]
  exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm.image_closure _

theorem cubeAntichainLaw_ae_geometry (n d : ℕ) :
    ∀ᵐ x ∂cubeAntichainLaw n d, (∀ j, x j ∈ cubePointSet d) ∧ IsAntichain x := by
  unfold cubeAntichainLaw
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae (ae_cubeSample_mem_cube n d),
    ae_restrict_mem (measurableSet_strictAntichainEvent n d)] with x hc ha
  exact ⟨fun j => hc j (mem_univ j), ha⟩

/-- Once the actual empirical weak concentration is supplied, the native
Euclidean Hausdorff exponential bound follows from the proved deterministic
finite tests and the actual conditional antichain law. -/
theorem euclidean_shape_concentration_of_weak {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (hWeak : ∀ U : Set (ProbabilityMeasure (CubePoint d)),
      U ∈ 𝓝 (limitingCubeProbability d) → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
        cubeAntichainLaw n d {x | empiricalCubeProbability n d x ∉ U} ≤
          ENNReal.ofReal (Real.exp (-α * (n : ℝ))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanSampleSet n d x)
        (euclideanLimitingSupport d)} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨U, hUopen, hUmem, hUshape⟩ := euclidean_shape_weak_neighborhood hd hδ
  obtain ⟨α, hα, htail⟩ := hWeak U (hUopen.mem_nhds hUmem)
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono_ae ?_) hn
  filter_upwards [cubeAntichainLaw_ae_geometry n d] with x hx
  intro hbad hmem
  exact not_lt_of_ge (hUshape n hnpos x hx.1 hx.2 hmem) hbad

/-- The full actual Hausdorff theorem, with the paper's Euclidean metric and
the genuine inverse-normal surface closure. All geometric detection and
empirical concentration steps are proved; only the cited alcove geometry
remains an explicit external input. -/
theorem euclidean_shape_exponential_concentration {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨α, hα, htail⟩ := euclidean_shape_concentration_of_weak hd
    (fun _ hU => empirical_cube_weak_concentration hd H hU) hδ
  rw [euclideanLimitingSupport_eq_closure_surface hd] at htail
  exact ⟨α, hα, htail⟩

end Antichain
