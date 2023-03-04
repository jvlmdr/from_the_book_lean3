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

noncomputable def harmonic (n : ℕ) := (finset.Icc 1 n).sum (λ k, (↑k)⁻¹ : ℕ → ℝ)
noncomputable def staircase (x : ℝ) := (⌊x⌋ : ℝ)⁻¹

-- To be used with antitone_on.interval_integrable.
lemma antitone_on_staircase {m n : ℝ} (hm : 1 ≤ m) (hn : 1 ≤ n) : antitone_on staircase (set.uIcc m n) :=
begin
  rw antitone_on_iff_forall_lt,
  intro a, intro ha,
  intro b, intro hb,
  have h1 := le_inf hm hn,
  have ha : 1 ≤ a := le_trans h1 ha.left,
  have hb : 1 ≤ b := le_trans h1 hb.left,
  intro hab,
  rw staircase, rw staircase,
  rw inv_le_inv,
      simp,
      rw int.le_floor,
      apply le_of_lt,
      exact lt_of_lt_of_le' hab (int.floor_le a),
    rw ← add_lt_add_iff_right (1 : ℝ), rw zero_add,
    apply lt_of_le_of_lt hb,
    apply int.lt_floor_add_one,
  rw ← add_lt_add_iff_right (1 : ℝ), rw zero_add,
  apply lt_of_le_of_lt ha,
  apply int.lt_floor_add_one,
end

-- Some way to avoid writing `measure_theory.measure_space.volume` in `interval_integrable?
-- variables {μ : measure_theory.measure ℝ} [measure_theory.is_locally_finite_measure μ]
-- noncomputable def μ : measure_theory.measure ℝ := measure_theory.measure_space.volume

lemma interval_integrable_staircase
  {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
  : interval_integrable staircase measure_theory.measure_space.volume a b
  := antitone_on.interval_integrable (antitone_on_staircase ha hb)

-- lemma interval_integrable_staircase
--   {μ : measure_theory.measure ℝ} [measure_theory.is_locally_finite_measure μ]
--   {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
--   : interval_integrable staircase μ a b
--   := antitone_on.interval_integrable (antitone_on_staircase ha hb)

-- lemma interval_integrable_staircase
--     {μ : measure_theory.measure ℝ} [measure_theory.is_locally_finite_measure μ]
--     {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
--   interval_integrable staircase μ a b :=
-- begin
--   apply antitone_on.interval_integrable,
--   exact antitone_on_staircase ha hb,
-- end


-- Given proofs of integral, prove value of integral.

-- Use this function to partition the integral into pieces.
def step (k : ℕ) := (k : ℝ)

noncomputable def const_fun (n : ℕ) : ℝ → ℝ := λ _, (n : ℝ)⁻¹

lemma staircase_part_eq_ae (n : ℕ) {μ : measure_theory.measure ℝ} :
  ∀ᵐ (x : ℝ) ∂μ, x ∈ set.uIoc (n : ℝ) (↑n + 1) → staircase x = const_fun n x :=
begin
  -- Just remains to prove this!
  sorry,
end

lemma integral_staircase_part_eq (n : ℕ) :
  ∫ (t : ℝ) in ↑n..↑n + 1, staircase t = (n : ℝ)⁻¹ :=
begin
  rw interval_integral.integral_congr_ae (staircase_part_eq_ae n),
  rw const_fun,
  simp,
end

-- Specialized for natural numbers.
-- (Could use finset.range instead and shift indices?)
lemma finset_Ico_succ {a b : ℕ} : finset.Ico a b.succ = finset.Icc a b :=
begin
  rw finset.ext_iff,
  intro x,
  rw finset.mem_Icc,
  rw finset.mem_Ico,
  rw nat.lt_succ_iff,
end

lemma integral_staircase_eq_harmonic {n : ℕ} :
  ∫ (t : ℝ) in 1..(↑n + 1), staircase t = harmonic n :=
begin
  simp,
  have ha : step 1 = 1 := by { rw step, simp },
  have hb : step (n + 1) = (↑n + 1) := by { rw step, simp },
  rw ← hb,
  rw ← ha,  -- Replaces (1 : ℝ) not (1 : ℕ).
  have hmn : 1 ≤ n + 1 := by simp,
  rw ← interval_integral.sum_integral_adjacent_intervals_Ico hmn,
    -- Need to prove sums are equal; ranges and values are equal.
    -- The integral functions have (step ...) inside.
    -- TODO: Avoid this line?
  { have h : (λ (k : ℕ), ∫ (x : ℝ) in step k..step (k + 1), staircase x) = (λ (n : ℕ), ∫ (t : ℝ) in ↑n..↑n + 1, staircase t) := _,
    { rw h,
      rw (function.funext_iff.mpr integral_staircase_part_eq),
      rw harmonic,
      rw finset_Ico_succ },
    { rw function.funext_iff,
      intro k,
      simp,
      rw step, rw step, simp } },
  { -- Prove each interval is integrable.
    intro k,
    intro hk,
    rw step, rw step, simp,
    have hp : (1 : ℝ) ≤ 1 := by simp,
    have hq : (1 : ℝ) ≤ ↑k + 1 := _,
    { apply interval_integrable.mono_set (interval_integrable_staircase hp hq),
      apply set.uIcc_subset_uIcc_right,
      simp, exact hk.left },
    { simp } },
end


-- Prove that integral of x → x⁻¹ is bounded above.

lemma inv_le_staircase {x : ℝ} : 1 ≤ x → x⁻¹ ≤ staircase x :=
begin
  rw staircase,
  intro hx,
  rw inv_le_inv,
  { apply int.floor_le },
  { apply lt_of_lt_of_le zero_lt_one hx },
  { rw ← add_lt_add_iff_right (1 : ℝ),
    rw zero_add,
    apply lt_of_le_of_lt hx,
    apply int.lt_floor_add_one },
end

lemma integral_inv_le_integral_staircase {x : ℝ} :
  1 ≤ x → ∫ (t : ℝ) in 1..x, t⁻¹ ≤ ∫ (t : ℝ) in 1..x, staircase t :=
begin
  intro hx,
  rw ← sub_nonneg,
  rw ← interval_integral.integral_sub,
  { apply interval_integral.integral_nonneg hx,
    intro u, intro hu,
    simp,
    apply inv_le_staircase hu.left },
  { apply interval_integrable_staircase _ hx, simp },
  { rw interval_integrable_inv_iff,
    apply or.inr,
    rw set.uIcc_of_le hx, simp,
    intro h, exfalso,
    exact not_le_of_lt zero_lt_one h }
end

lemma log_add_one_le_harmonic (n : ℕ) : log (↑n + 1) ≤ harmonic n :=
begin
  have hn : 1 ≤ (↑n + 1 : ℝ) := _,
    rw log_eq_integral_inv hn,
    apply le_trans (integral_inv_le_integral_staircase hn),
    rw integral_staircase_eq_harmonic,
  simp,
end
