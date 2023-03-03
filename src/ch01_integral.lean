import algebra
import analysis.special_functions.integrals
import analysis.special_functions.log.basic
import analysis.special_functions.log.deriv
import analysis.special_functions.non_integrable
import analysis.special_functions.trigonometric.basic
import data.real.basic
import data.nat.basic
import data.set.basic
import data.set.intervals.basic
import measure_theory.integral.integrable_on
import measure_theory.integral.interval_integral
import topology.algebra.order.floor

open real

lemma log_eq_integral_inv {x : ℝ} : 1 ≤ x → log x = ∫ (t : ℝ) in 1..x, t⁻¹ :=
begin
  intro hx,
  rw integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hx),
  simp,
end

-- noncomputable def harmonic : ℕ → ℝ
-- | 0 := 0
-- | (n+1) := (n.succ : ℝ)⁻¹ + harmonic n

-- noncomputable def inv_real (n : ℕ) := (n : ℝ)⁻¹
-- noncomputable def harmonic' (n : ℕ) := (finset.Icc 1 n).sum inv_real

noncomputable def harmonic (n : ℕ) := (finset.Icc 1 n).sum (λ k, (↑k)⁻¹ : ℕ → ℝ)

lemma harmonic_one : harmonic 1 = 1 :=
begin
  rw harmonic, simp,
end

noncomputable def real_ceil : ℝ → ℝ := λ x, ↑(int.ceil x)
noncomputable def inv_ceil := has_inv.inv ∘ real_ceil
def sub_one := λ (x : ℝ), x - 1
noncomputable def staircase := inv_ceil ∘ sub_one
noncomputable def inv_floor (x : ℝ) := (int.floor x : ℝ)⁻¹  -- Not continuous on (a, b].

lemma staircase_eq_on_local_Ioc (n : ℤ) :
  set.eq_on staircase (λ _, (n : ℝ)⁻¹) (set.Ioc ↑n (↑n + 1)) :=
begin
  rw set.eq_on,
  intro x,
  intro hx,
  rw staircase, simp,
  rw inv_ceil, rw sub_one, simp,
  rw real_ceil, simp,
  rw sub_eq_iff_eq_add,
  -- TODO: Better use of casts?
  have h : (n : ℝ) + 1 = ↑(n + 1) := by simp,
  rw h,
  have h' : ∀ {a b : ℤ}, (a : ℝ) = (b : ℝ) ↔ a = b := by simp,
  rw h',
  rw int.ceil_eq_iff, simp,
  exact hx,
end

-- inv_ceil = has_inv.inv ∘ real_ceil
-- Use 0 < n because this makes life easier.
lemma continuous_on_inv_ceil {n : ℕ} :
  0 < n → continuous_on inv_ceil (set.Ioc (↑n - 1) ↑n) :=
begin
  intro hn,
  rw inv_ceil, rw real_ceil,
  apply (
    continuous_on.comp continuous_on_inv₀ (continuous_on_ceil _)
    (_ : set.maps_to real_ceil _ _)
  ),
  simp,
  rw set.maps_to,
  intro x,
  cases n, simp at hn, contradiction,
  intro hx, simp at hx,
  rw real_ceil,
  simp,
  intro _,
  apply lt_of_le_of_lt _ hx.1,
  simp,
end

-- staircase = continuous_on_inv_ceil ∘ sub_one
lemma continuous_on_staircase_local {n : ℕ} :
  0 < n → continuous_on staircase (set.Ioc ↑n (↑n + 1)) :=
begin
  intro hn,
  rw staircase,
  apply (
    continuous_on.comp
    (continuous_on_inv_ceil hn)
    (continuous.continuous_on (continuous_sub_right 1))
    (_ : set.maps_to sub_one _ _)
  ),
  rw set.maps_to,
  intro x,
  intro hx, simp at hx,
  rw sub_one, simp,
  exact hx,
end

-- Like `continuous_on.integrable_on_Icc`, but for Ioc.
lemma integrable_on_of_continuous_on_Ioc {f : ℝ → ℝ} {a b : ℝ} (hf : continuous_on f (set.Ioc a b)) :
  measure_theory.integrable_on f (set.Ioc a b) :=
begin
  -- Can prove integrable on Icc as easily as Ioc.
  -- rw integrable_on_Icc_iff_integrable_on_Ioc,

  -- How?!
  -- Need to use continuous_on.ae_measurable?
  --
  -- `continuous_on.integrable_on_Icc` uses `hf.integrable_on_compact is_compact_Icc`
  -- `continuous_on.interval_integrable_of_Icc` uses `continuous_on.interval_integrable (uIcc.symm ???)`
  -- `measure_theory.integrable_on` uses `integrable f (μ.restrict s)`

  rw continuous_on at hf,
  -- have h_ae := continuous_on.ae_measurable hf measurable_set_Ioc,
  rw measure_theory.integrable_on,
  -- have h := measure_theory.integrable_on.restrict,
  sorry,  -- Assume for now.
end

lemma integral_staircase_local_eq :
  (λ (n : ℕ), ∫ (t : ℝ) in ↑n..↑n + 1, staircase t) = (λ (n : ℕ), (n : ℝ)⁻¹) :=
begin
  rw function.funext_iff,
  intro n,
  simp,
  have h_eq := staircase_eq_on_local_Ioc n, simp at h_eq,
  -- TODO: Could generalize and remove constraint?
  have h_le : ∀ {x : ℝ}, x ≤ x + 1 := by simp,
  rw interval_integral.integral_of_le h_le,
  -- Use congruence to constant function on interval.
  rw (
    measure_theory.set_integral_congr
    (measurable_set_Ioc : measurable_set (set.Ioc ↑n (↑n + 1)))
    h_eq
  ),
  simp,
end


-- Use this step to partition the integral into pieces.
def step (k : ℕ) := (k : ℝ)

lemma finset_Icc_eq_Ico_succ {a b : ℕ} : finset.Icc a b = finset.Ico a b.succ :=
begin
  rw finset.ext_iff,
  intro x,
  rw finset.mem_Icc,
  rw finset.mem_Ico,
  rw nat.lt_succ_iff,
end

lemma integrable_on_staircase_local {n : ℕ} (hn : 0 < n) :
  measure_theory.integrable_on staircase (set.Ioc n (↑n + 1)) :=
begin
  apply integrable_on_of_continuous_on_Ioc,
  apply continuous_on_staircase_local hn,
end

lemma integrable_on_staircase {n : ℕ} :
  measure_theory.integrable_on staircase (set.Ioc 1 (↑n + 1)) :=
begin
  have hab : (1 : ℝ) ≤ (↑n + 1) := by simp,
  rw ← interval_integrable_iff_integrable_Ioc_of_le hab,
  have ha : step 1 = 1 := by { rw step, simp },
  have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
  rw ← hb,
  rw ← ha,
  have hmn : 1 ≤ n + 1 := by simp,
  apply interval_integrable.trans_iterate_Ico hmn,
  intro k, intro hk, rw step, rw step,
  simp,
  have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by simp,
  rw interval_integrable_iff_integrable_Ioc_of_le hkk,
  have hk' : 0 < k := lt_of_lt_of_le zero_lt_one hk.left,
  apply integrable_on_staircase_local hk',
end

lemma interval_integrable_staircase_local {n : ℕ} (hn : 0 < n) :
  interval_integrable staircase measure_theory.measure_space.volume ↑n (↑n + 1) :=
begin
  have hnn : (n : ℝ) ≤ (↑n + 1) := by simp,
  rw interval_integrable_iff_integrable_Ioc_of_le hnn,
  apply integrable_on_of_continuous_on_Ioc,
  apply continuous_on_staircase_local hn,
end

lemma interval_integrable_staircase {n : ℕ} :
  interval_integrable staircase measure_theory.measure_space.volume 1 (↑n + 1) :=
begin
  -- have hab : (1 : ℝ) ≤ (↑n + 1) := by simp,
  -- rw ← interval_integrable_iff_integrable_Ioc_of_le hab,
  have ha : step 1 = 1 := by { rw step, simp },
  have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
  rw ← hb,
  rw ← ha,
  have hmn : 1 ≤ n + 1 := by simp,
  apply interval_integrable.trans_iterate_Ico hmn,
  intro k, intro hk, rw step, rw step,
  simp,
  have hk' : 0 < k := lt_of_lt_of_le zero_lt_one hk.left,
  apply interval_integrable_staircase_local hk',
end


lemma integral_staircase_eq_harmonic {n : ℕ} :
  ∫ (t : ℝ) in 1..(↑n + 1), staircase t = harmonic n :=
begin
  simp,
  -- Convert 1..(↑n+1) to (step 1)..(step (n+1)) to use sum_integral_adjacent_intervals_Ico.
  have ha : step 1 = 1 := by { rw step, simp },
  have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
  rw ← hb,
  rw ← ha,  -- Replaces (1 : ℝ) not (1 : ℕ).
  have hmn : 1 ≤ n + 1 := by simp,
  rw ← interval_integral.sum_integral_adjacent_intervals_Ico hmn,
    -- Need to prove sums are equal; ranges and values are equal.
    -- The integral functions have (step ...) inside.
    -- TODO: Avoid this line?
    have h : (λ (k : ℕ), ∫ (x : ℝ) in step k..step (k + 1), staircase x) = (λ (n : ℕ), ∫ (t : ℝ) in ↑n..↑n + 1, staircase t) := _,
      rw h,
      rw integral_staircase_local_eq,
      rw harmonic,
      rw finset_Icc_eq_Ico_succ,
    rw function.funext_iff,
    intro k,
    simp,  -- interval_integral ...
    rw step, rw step, simp,
  -- Prove each interval is integrable.
  intro k,
  intro hk,
  rw step, rw step, simp,
  have hkk : (k : ℝ) ≤ ↑k + 1 := by simp,
  rw interval_integrable_iff_integrable_Ioc_of_le hkk,
  have hk' : 0 < k := lt_of_lt_of_le zero_lt_one hk.left,
  apply integrable_on_staircase_local hk',
end

-- lemma interval_integrable_staircase {x : ℝ} {μ : measure_theory.measure ℝ} :
--   1 ≤ x → interval_integrable staircase μ 1 x :=
-- begin
--   intro hx,
--   generalize hn : ⌊x⌋₊ + 1 = n,
--   have h1n : 1 ≤ n := _,
--     have hxn : x ≤ ↑n := _,
--       have ha : step 1 = 1 := by { rw step, simp },
--       have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
--       -- apply interval_integrable.trans_iterate,
--       sorry,
--     sorry,
--   sorry,
-- end

-- lemma interval_integrable_staircase {n : ℕ} :
--   @interval_integrable ℝ _ staircase measure_theory.measure_space.volume 1 (↑n + 1) :=
-- begin
--   have ha : step 1 = 1 := by { rw step, simp },
--   have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
--   rw ← hb,
--   rw ← ha,
--   apply interval_integrable.trans_iterate_Ico,
--     simp,
--   intro k,
--   intro hk,
--   rw step,
--   rw step,
--   have h := @interval_integrable_staircase_local k (_ : 0 < k),
--     exact h,  -- Why does this timeout?
--   sorry,
--   -- apply @interval_integrable_staircase_local k,
--   -- simp,
-- end

lemma inv_le_staircase {x : ℝ} : 1 < x → x⁻¹ ≤ staircase x :=
begin
  rw staircase,
  rw [inv_ceil, sub_one],
  rw real_ceil, simp,
  intro hx,
  rw inv_le_inv _ _,
      rw sub_le_iff_le_add,
      apply le_of_lt,
      apply int.ceil_lt_add_one,
    apply lt_trans zero_lt_one hx,
  rw lt_sub_iff_add_lt, simp,
  apply lt_of_lt_of_le hx,
  apply int.le_ceil,
end

lemma integral_inv_le_integral_staircase {x : ℝ} :
  1 ≤ x → ∫ (t : ℝ) in 1..x, t⁻¹ ≤ ∫ (t : ℝ) in 1..x, staircase t :=
begin
  intro hx,
  -- rw sub_le_zero,  -- Doesn't exist? Only sub_lt_zero?
  have h : ∀ {a b : ℝ}, a ≤ b ↔ 0 ≤ b - a := by simp,
  rw h,
  rw ← interval_integral.integral_sub,
      rw interval_integral.integral_of_le hx,
      apply (measure_theory.set_integral_nonneg
             (measurable_set_Ioc : measurable_set (set.Ioc 1 x))),
      intro u, intro hu,
      simp,
      apply inv_le_staircase,
      simp at hu,
      exact hu.1,
    -- Still need proof that staircase is integrable.
    simp,
    rw interval_integrable_iff_integrable_Ioc_of_le hx,
    have hs : set.Ioc (1 : ℝ) x ⊆ set.Ioc (1 : ℝ) (↑⌊x⌋₊ + 1) := _,
      apply measure_theory.integrable_on.mono_set _ hs,
      apply integrable_on_staircase,
    apply set.Ioc_subset_Ioc_right,
    rw nat.cast_floor_eq_cast_int_floor (le_trans zero_le_one hx),
    apply le_trans (int.le_ceil x),
    have h := int.ceil_le_floor_add_one x,
    rw ← @int.cast_le ℝ at h,
    simp at h, exact h,
  rw interval_integrable_inv_iff,
  apply or.inr,
  rw set.uIcc_of_le hx,
  rw set.mem_Icc,
  intro h,
  exact not_le_of_lt zero_lt_one h.left,
end

lemma log_add_one_le_harmonic (n : ℕ) : log (↑n + 1) ≤ harmonic n :=
begin
  have hn : 1 ≤ (↑n + 1 : ℝ) := _,
    rw log_eq_integral_inv hn,
    apply le_trans (integral_inv_le_integral_staircase hn),
    rw integral_staircase_eq_harmonic,
  simp,
end
