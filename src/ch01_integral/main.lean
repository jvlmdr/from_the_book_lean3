import .infinite_sums
import .log_harmonic
import .factors_le

import data.finset.image
import data.pnat.defs
import data.real.ennreal
import order.filter.basic
import order.filter.at_top_bot
import algebra.big_operators.basic
import topology.algebra.infinite_sum

open real filter
open_locale big_operators


lemma prod_geom_series_primes_eq (n : ℕ) :
  ∏ p in primes_le n, ((1 - (↑p)⁻¹)⁻¹ : ℝ) ≤
  ↑(finset.card (primes_le n) + 1) :=
begin
  sorry,
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
