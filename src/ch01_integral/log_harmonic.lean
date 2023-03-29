import analysis.special_functions.integrals
import analysis.special_functions.non_integrable
import data.real.basic
import data.nat.basic
import data.int.basic
import data.set.basic
import data.set.intervals.basic
import measure_theory.integral.interval_integral

open real measure_theory

lemma log_eq_integral_inv {x : ℝ} : 1 ≤ x → log x = ∫ (t : ℝ) in 1..x, t⁻¹ :=
begin
  intro hx,
  rw integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hx),
  simp,
end

noncomputable def harmonic (n : ℕ) : nnreal := (finset.Icc 1 n).sum (λ k, (↑k)⁻¹)

noncomputable def staircase (x : ℝ) : ℝ := (↑⌊x⌋)⁻¹


-- Show that staircase is antitone on [1, ∞).
-- This will be used to show that it is integrable.

lemma antitone_on_staircase : antitone_on staircase (set.Ici 1) :=
begin
  rw antitone_on_iff_forall_lt,
  simp,
  intro a, intro ha,
  intro b, intro hb,
  intro hab,
  rw staircase, rw staircase,
  rw inv_le_inv,
  { simp,
    rw int.le_floor,
    have h := int.floor_le a,
    exact le_trans h (le_of_lt hab) },
  { have h := int.lt_floor_add_one b,
    rw ← add_lt_add_iff_right (1 : ℝ), rw zero_add,
    exact lt_of_le_of_lt hb h },
  { have h := int.lt_floor_add_one a,
    rw ← add_lt_add_iff_right (1 : ℝ), rw zero_add,
    exact lt_of_le_of_lt ha h },
end

-- To be used with antitone_on.interval_integrable.
lemma antitone_on_staircase_uIcc {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  antitone_on staircase (set.uIcc a b) :=
begin
  apply antitone_on.mono antitone_on_staircase,
  cases le_or_lt a b with hab hba,
  { rw set.uIcc_of_le hab,
    rw set.Icc_subset_Ici_iff hab,
    exact ha },
  { have hba := le_of_lt hba,
    rw set.uIcc_comm,
    rw set.uIcc_of_le hba,
    rw set.Icc_subset_Ici_iff hba,
    exact hb },
end

-- Trivial but used in two places.
lemma interval_integrable_staircase {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
  : interval_integrable staircase volume a b :=
begin
  apply antitone_on.interval_integrable,
  apply antitone_on_staircase_uIcc ha hb,
end


-- After proving staircase is integrable, prove value of integral.

noncomputable def const_fun (n : ℕ) : ℝ → ℝ := λ _, (n : ℝ)⁻¹

lemma piece_integral_staircase_eq {n : ℕ} :
  ∫ (t : ℝ) in ↑n..↑n + 1, staircase t = (n : ℝ)⁻¹ :=
begin
  -- rw interval_integral.integral_of_le (by simp : (n : ℝ) ≤ (n : ℝ) + 1),
  rw interval_integral.integral_congr_ae
    (_ : ∀ᵐ (x : ℝ) ∂_, x ∈ _ → staircase x = const_fun n x),
  { rw const_fun, simp, },
  { -- Need to prove staircase is ae-equal to const_fun in the interval.
    rw ae_iff,
    -- Use volume set ≤ volume {b} = 0.
    rw ← le_zero_iff,
    apply le_of_le_of_eq (measure_mono (_ : _ ⊆ ({↑n + 1} : set ℝ))),
    { exact volume_singleton, },
    { simp,
      intros x hax hxb hnp,
      rw le_iff_lt_or_eq at hxb,
      cases hxb,
      { exfalso,
        apply hnp,
        rw [staircase, const_fun], simp,
        rw [← int.cast_coe_nat, int.cast_inj],
        rw int.floor_eq_iff, simp,
        apply and.intro _ hxb,
        exact le_of_lt hax, },
      { exact hxb, }, }, },
end

-- Specialized for natural numbers.
-- (Could use finset.range instead and shift indices?)
lemma finset_Ico_succ {a b : ℕ} : finset.Ico a b.succ = finset.Icc a b :=
begin
  ext x,
  rw finset.mem_Icc,
  rw finset.mem_Ico,
  rw nat.lt_succ_iff,
end

-- Use this function to partition the integral into pieces.
def step (k : ℕ) := (k : ℝ)

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
  { -- Prove sums are equal.
    simp_rw step,
    push_cast,
    simp_rw piece_integral_staircase_eq,
    rw harmonic,
    push_cast,
    rw finset_Ico_succ, },
  { -- Prove each interval is integrable.
    simp_rw step,
    push_cast,
    intros k hk,
    have hp : (1 : ℝ) ≤ 1 := by simp,
    have hq : (1 : ℝ) ≤ ↑k + 1 := by simp,
    -- TODO: Use mono?
    apply interval_integrable.mono_set (interval_integrable_staircase hp hq),
    apply set.uIcc_subset_uIcc_right,
    simp, exact hk.left, },
end


-- Prove that integral of x⁻¹ is less than integral of staircase.

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

-- Could instead prove ∀ x : ℝ, log x ≤ harmonic ⌊x⌋₊
-- However, the proof only requires a proof for integer values.
lemma log_add_one_le_harmonic {n : ℕ} : log (↑n + 1) ≤ harmonic n :=
begin
  have hn : (1 : ℝ) ≤ (↑n + 1) := by simp,
  rw log_eq_integral_inv hn,
  apply le_trans (integral_inv_le_integral_staircase hn),
  rw integral_staircase_eq_harmonic,
end
