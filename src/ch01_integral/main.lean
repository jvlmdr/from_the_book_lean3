import .infinite_sums
import .log_harmonic
import .factors_le

import data.finset.image
import data.pnat.defs
import data.real.basic
import data.real.nnreal
import data.real.ennreal
import data.set.intervals.basic
import data.nat.interval
import order.filter.basic
import order.filter.at_top_bot
import order.monotone.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import algebra.group.basic
import algebra.order.positive.field
import algebra.field.defs

open real filter
open_locale big_operators


def prime_index (p : nat.primes) : ℕ := finset.card (primes_le ↑p)

#eval prime_index ⟨2, nat.prime_two⟩
#eval prime_index ⟨3, nat.prime_three⟩

-- Could instead use fact that 1/(p-1) is antitone (on p > 1)?
-- p / (p-1) = 1 + 1/(p-1) ≤ 1 + 1/k = (k+1)/k
lemma antitone_on_div_sub_one : antitone_on (λ x, ↑x / (↑x - 1) : ℕ → ℝ) (set.Ioi 1) :=
begin
  simp [antitone_on],
  intros a ha b hb h,
  rw div_le_div_iff,
  { simp [mul_sub, mul_comm], exact h, },
  { simp, exact hb, },
  { simp, exact ha, },
end

lemma prime_index_le_prime {p : nat.primes} : prime_index p + 1 ≤ ↑p :=
begin
  sorry,
end

-- lemma zero_lt_coe_pnat (x : ℕ+) : (↑x : nnreal) > 0 :=
-- begin
--   norm_cast,
--   exact x.prop,
-- end

-- def inv_coe_pos (x : ℕ+) : {y : ℝ // y > 0} := ⟨↑x, zero_lt_coe_pnat x⟩

-- noncomputable instance linear_ordered_comm_group_pos : linear_ordered_comm_group {x : ℝ // 0 < x} :=
--   positive.subtype.linear_ordered_comm_group

noncomputable instance real_semifield : semifield ℝ := field.to_semifield

noncomputable instance real_comm_group_with_zero : comm_group_with_zero ℝ := semifield.to_comm_group_with_zero ℝ

instance comm_group_nonzero : comm_group {x : ℝ // x ≠ 0} := sorry

instance can_lift_nonzero : can_lift ℝ {x : ℝ // x ≠ 0} _ _ := subtype.can_lift _

-- `finset.prod_range_div` requires `comm_group` (must exclude zero).
lemma finset_prod_range_div_of_ne_zero (f : ℕ → ℝ) (n : ℕ) (h_pos : ∀ k, f k ≠ 0) :
  (finset.range n).prod (λ (i : ℕ), f (i + 1) / f i) = f n / f 0 :=
begin
  have h : ∀ (k : ℕ), f k = ↑(⟨f k, h_pos k⟩ : {x : ℝ // x ≠ 0}) := by simp,
  have h' : ∀ (j k : ℕ), f j / f k = ↑(⟨f j / f k, h_pos (f j / f k)⟩ : {x : ℝ // x ≠ 0}),  -- Can obtain as subgroup_with_zero?
  sorry,
end

lemma finset_Icc_eq_image_succ_range : ∀ {k : ℕ}, finset.Icc 1 k = finset.image nat.succ (finset.range k) :=
begin
  intro k,
  -- have h := finset.map_eq_image ⟨nat.succ, nat.succ_injective⟩ (finset.range k),
  -- rw [finset.range_eq_Ico, ← nat.Ico_succ_right],
  ext, simp,
  apply iff.intro,
  { intro h,
    cases h with ha hk,
    cases a,
    { exfalso, revert ha, simp, },
    existsi a,
    simp at *,
    exact hk, },
  { intro h,
    cases h with b hb,
    cases hb with hk ha,
    rw ← ha, clear ha,
    simp [nat.succ_le_succ_iff],
    exact hk, },
end

lemma prod_geom_series_primes_eq (n : ℕ) :
  ∏ p in primes_le n, ((1 - (↑p)⁻¹)⁻¹ : ℝ) ≤
  ↑(finset.card (primes_le n) + 1) :=
begin
  have h : ∏ p in primes_le n, ((1 - (↑p)⁻¹)⁻¹ : ℝ) = ∏ p in primes_le n, ↑p / (↑p - 1),
  { sorry, },
  rw h, clear h,
  -- have h : ∏ p in primes_le n, (↑p / (↑p - 1) : ℝ) ≤ ∏ k in finset.Icc 1 (finset.card (primes_le n)), (↑k + 1) / ↑k,
  -- { sorry, },
  have h : ∏ p in primes_le n, (↑p / (↑p - 1) : ℝ) ≤ ∏ k in finset.Icc 1 (finset.card (primes_le n)), (↑k + 1) / ↑k,
  { sorry, },
  apply le_trans h, clear h,
  apply le_of_eq,
  have h := finset_prod_range_div_of_ne_zero (λ x, (↑x + 1 : ℝ)) (primes_le n).card _,
  rotate, { norm_cast, simp, },
  simp [-finset.prod_div_distrib] at h,
  norm_cast at h,
  rw ← h, clear h,
  rw finset_Icc_eq_image_succ_range,
  rw finset.prod_image,
  { simp, },
  simp,
end

-- def pnat_range (n : ℕ) : finset ℕ+ := finset.image nat.to_pnat' (finset.Icc 1 n)
--
-- lemma coe_pnat_range_eq {n : ℕ} : finset.image coe (pnat_range n) = finset.Icc 1 n :=
-- begin
--   rw pnat_range,
--   simp [finset.image_image],
--   rw (_ : finset.image (coe ∘ nat.to_pnat') (finset.Icc 1 n) = finset.image id (finset.Icc 1 n)),
--   { simp, },
--   apply finset.image_congr,
--   simp [set.eq_on],
--   intros x h1 h2 h3,
--   exfalso,
--   revert h1,
--   simp [h3],
-- end

lemma mem_pnat_fac_le_of_mem_Icc {n : ℕ} {x : ℕ} (hx : x ∈ finset.Icc 1 n) : (nat.to_pnat' x ∈ pnat_fac_le n) :=
begin
  simp [pnat_fac_le],
  cases x,
  { exfalso, revert hx, simp, },
  apply all_factors_le_of_le,
  simp at *,
  exact hx.right,
end

def pnat_fac_le_range (n : ℕ) : finset ↥(pnat_fac_le n) :=
  -- finset.image (λ x, ⟨nat.to_pnat' x.val, mem_pnat_fac_le_of_mem_Icc x.property⟩) (finset.Icc 1 n).attach
  (finset.Icc 1 n).attach.image (λ x, ⟨nat.to_pnat' x.val, mem_pnat_fac_le_of_mem_Icc x.property⟩)

lemma coe_pnat_fac_le_range_eq {n : ℕ} : finset.image coe (pnat_fac_le_range n) = finset.Icc 1 n :=
begin
  rw (_ : finset.image coe (pnat_fac_le_range n) = finset.image coe (finset.Icc 1 n).attach),
  { rw finset.attach_image_coe, },
  rw pnat_fac_le_range,
  rw finset.image_image,
  apply finset.image_congr,
  simp [set.eq_on],
  intros a ha _ h,
  exfalso,
  revert ha,
  rw h,
  simp,
end

-- lemma nnreal_sum_le_tsum {α : Type*} {f : α → nnreal} (s : finset α) :
--   s.sum (λ (x : α), f x) ≤ ∑' (x : α), f x :=
-- begin
--   -- Should be easy to prove this? Non-negative! Needs summable?!
--   rw sum_eq_tsum_indicator,
--   sorry,
-- end

lemma finset_sum_inv_le_tsum_pnat_inv {n : ℕ} :
  -- ∑ k : ℕ+ in finset.Icc 1 n, ((↑k)⁻¹ : nnreal) ≤ 
  harmonic n ≤ ∑' k : ↥(pnat_fac_le n), (↑k)⁻¹ :=
begin
  rw harmonic,
  rw ← coe_pnat_fac_le_range_eq,
  rw finset.sum_image,
  { rw ← ennreal.coe_le_coe,
    push_cast,
    -- Should be possible to avoid need for summable proof here?
    rw ennreal.coe_tsum (sum_inv_pnat_fac_le_eq_prod_geom_series n).summable,
    apply ennreal.sum_le_tsum, },
  { simp, },
end

lemma log_le_card_primes {n : ℕ} : 
  log (↑n + 1) ≤ ↑(finset.card (primes_le n) + 1) :=
begin
  apply le_trans log_add_one_le_harmonic,
  norm_cast,
  apply le_trans finset_sum_inv_le_tsum_pnat_inv,
  -- rw (by simp : ∀ {x : ℕ}, (↑x : ℝ) = ((↑x : nnreal) : ℝ)),
  -- norm_cast,
  rw has_sum.tsum_eq (sum_inv_pnat_fac_le_eq_prod_geom_series n),
  apply le_trans _ (prod_geom_series_primes_eq _),
  push_cast,
  apply le_of_eq,
  apply finset.prod_congr rfl,
  intros p _,
  simp,
  rw nnreal.coe_sub _,
  { simp, },
  simp,
  norm_cast,
  simp,
end


theorem infinite_primes : tendsto (λ n, finset.card (primes_le n)) at_top at_top :=
begin
  sorry,
end
