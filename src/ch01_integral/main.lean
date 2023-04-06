import .infinite_sums
import .log_harmonic
import .factors_le

import data.finset.image
import data.finset.card
import data.pnat.defs
import data.real.basic
import data.real.nnreal
import data.real.ennreal
import data.set.intervals.basic
import data.set.function
import data.nat.interval
import data.subtype
import order.filter.basic
import order.filter.at_top_bot
import order.filter.archimedean
import order.basic
import order.monotone.basic
import algebra.big_operators.basic
import algebra.group.basic
import algebra.group_with_zero.defs
import algebra.order.positive.field
import algebra.field.defs
import algebra.hom.group
import topology.algebra.infinite_sum
import topology.algebra.monoid
import analysis.special_functions.log.basic

open real filter
open_locale big_operators


def prime_index (p : nat.primes) : ℕ := finset.card (primes_le ↑p)
-- def prime_index : nat.primes → ℕ := λ p, finset.card (primes_le ↑p)

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

-- noncomputable instance linear_ordered_comm_group_positive : linear_ordered_comm_group {x : ℝ // 0 < x} :=
--   positive.subtype.linear_ordered_comm_group
-- noncomputable instance linear_ordered_cancel_comm_monoid_positive : linear_ordered_cancel_comm_monoid {x : ℝ // 0 < x} :=
--   positive.subtype.linear_ordered_cancel_comm_monoid
-- instance ordered_comm_monoid_positive : ordered_comm_monoid {x : ℝ // 0 < x} :=
--   positive.subtype.ordered_comm_monoid

instance comm_monoid_positive : comm_monoid {x : ℝ // 0 < x} :=
  ordered_comm_monoid.to_comm_monoid _

-- nonneg.coe_div
@[simp, norm_cast]
lemma positive_coe_div {a b : {x : ℝ // 0 < x}} : (↑(a / b) : ℝ) = ↑a / ↑b := rfl

-- def positive_coe_hom : {x : ℝ // 0 < x} →+* ℝ := ⟨coe, coe_one, coe_mul, coe_add⟩

-- Modelled on: `nnrat.coe_hom`, `inv_monoid_hom`
def positive_coe_hom : {x : ℝ // 0 < x} →* ℝ :=
{ to_fun := (λ x, x.val),
  map_one' := by simp,
  map_mul' := by simp, }

-- Modelled on: `nnrat.coe_prod`
@[norm_cast]
theorem positive_coe_prod {α : Type*} {s : finset α} {f : α → {x : ℝ // 0 < x}} :
  (↑(s.prod f) : ℝ) = ∏ (a : α) in s, ↑(f a) :=
begin
  -- Want equivalent of `ring_hom.map_prod`...
  have h := positive_coe_hom.map_prod f,
  simp [positive_coe_hom] at h,
  exact h _,
end

-- TODO: Should be possible to prove with non-zero rather than positive.
-- However, I couldn't find the right lemmas to make this easy.
-- We can show that ℝ is instance of comm_group_with_zero... where to then?

-- noncomputable instance real_semifield : semifield ℝ := field.to_semifield
-- noncomputable instance real_comm_group_with_zero : comm_group_with_zero ℝ := semifield.to_comm_group_with_zero ℝ
-- lemma finset_prod_range_div_of_ne_zero (f : ℕ → ℝ) (n : ℕ) (h_nonzero : ∀ k, f k ≠ 0) :
--   (finset.range n).prod (λ i, f (i+1) / f i) = f n / f 0 :=

-- `finset.prod_range_div` requires `comm_group` (must exclude zero).
lemma finset_prod_range_div_of_positive (f : ℕ → ℝ) (n : ℕ) (hf : ∀ k, 0 < f k) :
  (finset.range n).prod (λ i, f (i+1) / f i) = f n / f 0 :=
begin
  have h := finset.prod_range_div (λ i, (⟨f i, hf i⟩ : {x : ℝ // 0 < x})) n,
  simp [-finset.prod_div_distrib] at h,
  rw ← subtype.coe_inj at h,
  simp [positive_coe_prod, -finset.prod_div_distrib] at h,
  exact h,
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

lemma div_sub_one_eq {x : ℝ} : 1 < x → (1 - x⁻¹)⁻¹ = x / (x - 1) :=
begin
  intro hx,
  have hx' := inv_lt_one hx,
  have hx'' := lt_trans zero_lt_one hx,
  rw inv_eq_one_div,
  rw div_eq_div_iff (has_lt.lt.ne' (sub_pos_of_lt hx')) (has_lt.lt.ne' (sub_pos_of_lt hx)),
  simp [mul_sub],
  rw mul_inv_cancel (has_lt.lt.ne' hx''),
end

lemma primes_le_mono : monotone primes_le :=
begin
  simp [monotone],
  intros a b h,
  simp [primes_le],
  apply finset.subtype_mono,
  apply finset.range_mono,
  simp,
  exact h,
end

@[simp]
lemma primes_le_two_eq : (primes_le 2) = {⟨2, nat.prime_two⟩} :=
begin
  simp [primes_le],
  ext,
  simp,
  have h := nat.prime.two_le a.prop,
  rw nat.lt_succ_iff,
  rw has_le.le.le_iff_eq h,
  rw ← nat.primes.coe_nat_inj,
  simp,
end

lemma two_mem_primes_le_prime {p : nat.primes} : (⟨2, nat.prime_two⟩ : nat.primes) ∈ primes_le ↑p :=
begin
  simp [primes_le],
  rw nat.lt_succ_iff,
  apply nat.prime.two_le p.prop,
end

@[simp]
lemma nonempty_primes_le_prime {p : nat.primes} : finset.nonempty (primes_le ↑p) :=
begin
  rw finset.nonempty,
  existsi (⟨2, nat.prime_two⟩ : nat.primes),
  exact two_mem_primes_le_prime,
end

@[simp]
lemma mem_primes_le_self (p : nat.primes) : p ∈ primes_le p := by simp [primes_le]

namespace primes_le
lemma not_mem_of_lt {n : ℕ} {q : nat.primes} (h_lt : n < ↑q) : q ∉ primes_le n :=
begin
  rw primes_le,
  intro h,
  simp at h,
  cases q with q hq,
  simp at *,
  clear hq,
  linarith,
end
end primes_le

-- Needed for strict_mono.
instance preorder_primes : preorder nat.primes := subtype.preorder _

-- TODO: Remove?
namespace primes_le
lemma not_mem_of_lt_prime {p q : nat.primes} (h_lt : p < q) : q ∉ primes_le ↑p :=
begin
  apply not_mem_of_lt,
  norm_cast,
  exact h_lt,
end
end primes_le

lemma prime_index_strict_mono : strict_mono prime_index :=
begin
  simp [strict_mono, prime_index],
  intros p q h,
  apply finset.card_lt_card,
  rw finset.ssubset_iff_of_subset _,
  { existsi q,
    have hq := mem_primes_le_self q,
    existsi hq,
    apply primes_le.not_mem_of_lt_prime h, },
  { apply primes_le_mono,
    simp,
    exact le_of_lt h, },
end

-- Needed for function.injective.
instance linear_order_primes : linear_order nat.primes := subtype.linear_order _

lemma prime_index_injective : function.injective prime_index := strict_mono.injective prime_index_strict_mono

lemma card_primes_le_succ_le {n : ℕ} : (primes_le n.succ).card ≤ (primes_le n).card.succ :=
begin
  simp [primes_le],
  rw finset.range_succ,
  simp [nat.add_one],
  rw finset.filter_insert,
  rw apply_ite finset.card,
  simp [nat.add_one],
  apply le_trans (ite_le_sup _ _ _),
  simp,
  apply nat.le_succ,
end

lemma prime_index_le_prime {p : nat.primes} : prime_index p + 1 ≤ ↑p :=
begin
  cases p with n h,
  revert h,
  simp [prime_index],
  intro h,
  replace h := nat.prime.two_le h,
  replace h := nat.lt_of_succ_le h,
  replace h := ne_zero_of_lt h,
  revert h,
  cases n,
  { simp, },
  simp [nat.succ_le_succ_iff],
  induction n with k h,
  { simp [primes_le, finset.filter_eq_empty_iff],
    intros p h2 hp,
    replace hp := nat.prime.two_le hp,
    linarith, },
  apply le_trans card_primes_le_succ_le,
  rw nat.succ_le_succ_iff,
  apply h,
end

lemma prime_index_surj_on {n : ℕ} : ∀ i, i ∈ finset.Icc 1 (primes_le n).card → (∃ (p : nat.primes) (hp : p ∈ primes_le n), i = prime_index p) :=
begin
  apply finset.surj_on_of_inj_on_of_card_le,
  { -- maps_to (?)
    intros p hp,
    simp [prime_index],
    apply and.intro,
    { rw nat.succ_le_iff,
      rw finset.card_pos,
      apply nonempty_primes_le_prime, },
    { mono,
      apply primes_le_mono,
      revert hp,
      simp [primes_le, nat.lt_succ_iff], }, },
  { -- inj_on
    intros p q hp hq,
    apply prime_index_injective, },
  { -- card_le
    simp, },
end

lemma image_prime_index_eq_Icc {n : ℕ} : finset.image prime_index (primes_le n) = finset.Icc 1 (primes_le n).card :=
begin
  ext i,
  apply iff.intro,
  { simp [prime_index],
    intros p hp hi,
    rw ← hi, clear hi,
    apply and.intro,
    { simp [nat.succ_le_iff, finset.card_pos], },
    { mono,
      apply primes_le_mono,
      revert hp,
      simp [primes_le, nat.lt_succ_iff], }, },
  { intro hi,
    simp,
    have h := prime_index_surj_on i hi,
    cases h with p hp,  -- Is this a non-constructive proof?
    existsi p,
    cases hp with hp hi,
    refine and.intro hp _,
    rw eq_comm,
    exact hi, },
end

lemma prod_primes_le_prod_Icc {n : ℕ} : ∏ p in primes_le n, (↑p / (↑p - 1) : ℝ) ≤ ∏ k in finset.Icc 1 (finset.card (primes_le n)), (↑k + 1) / ↑k :=
begin
  have h' : ∀ (p : nat.primes), (↑p / (↑p - 1) : ℝ) ≤ (↑(prime_index p + 1)) / (↑(prime_index p + 1) - 1),
  { intro p,
    have h : (↑p : ℝ) = ↑(↑p : ℕ),
    { norm_cast, },
    rw h, clear h,
    apply antitone_on_div_sub_one,
    { simp [prime_index, finset.card_pos], },
    { simp, exact nat.prime.one_lt p.prop, },
    { exact prime_index_le_prime, }, },
  have h : ∏ p in primes_le n, (↑p / (↑p - 1) : ℝ) ≤ ∏ p in primes_le n, (↑(prime_index p + 1)) / (↑(prime_index p + 1) - 1),
  { apply finset.prod_le_prod,
    { intros p hp,
      have h : (1 : ℝ) < ↑p,
      { norm_cast, exact nat.prime.one_lt p.prop, },
      apply div_nonneg,
      { simp, },
      { rw sub_nonneg, exact le_of_lt h, }, },
    { intros p hp,
      exact h' _, }, },
  clear h',
  apply le_trans h, clear h,
  apply le_of_eq,
  push_cast,
  simp_rw add_sub_cancel,
  -- Should use `finset.prod_bij`?
  -- simp [-finset.prod_div_distrib],
  rw ← image_prime_index_eq_Icc,
  rw finset.prod_image,
  intros p hp q hq,
  apply prime_index_injective,
end

lemma prod_geom_series_primes_eq (n : ℕ) :
  ∏ p in primes_le n, ((1 - (↑p)⁻¹)⁻¹ : ℝ) ≤
  ↑(finset.card (primes_le n) + 1) :=
begin
  have h : ∀ (p : nat.primes), ((1 - (↑p)⁻¹)⁻¹ : ℝ) = ↑p / (↑p - 1),
  { intro p,
    apply div_sub_one_eq,
    norm_cast,
    exact nat.prime.one_lt p.prop, },
  simp_rw h, clear h,
  apply le_trans prod_primes_le_prod_Icc,
  apply le_of_eq,
  have h := finset_prod_range_div_of_positive (λ x, (↑x + 1 : ℝ)) (primes_le n).card _,
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

lemma log_succ_le_succ_card_primes (n : ℕ) : log (↑n.succ) ≤ ↑(primes_le n).card.succ :=
begin
  push_cast,
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


lemma tendsto_log_coe_nat : tendsto (λ (n : ℕ), log ↑n) at_top at_top :=
begin
  rw ← filter.tendsto_map'_iff,
  sorry,
end

-- Should be possible to remove nat constraint?
lemma tendsto_nat_add {β : Type*} [preorder β] {f : ℕ → β} (d : ℕ) :
  tendsto (λ k, f (k + d)) at_top at_top ↔ tendsto f at_top at_top :=
begin
  rw ← filter.tendsto_map'_iff,
  sorry,
end

lemma tendsto_add_const_at_top {α : Type*} [preorder α] {f : α → ℝ} (c : ℝ) :
  tendsto (λ x, f x + c) at_top at_top ↔ tendsto f at_top at_top :=
begin
  -- rw filter.tendsto.const_add,
  sorry,
end

theorem infinite_primes : tendsto (λ n, finset.card (primes_le n)) at_top at_top :=
begin
  rw ← @tendsto_coe_nat_at_top_iff _ ℝ,
  rw ← tendsto_add_const_at_top 1,
  norm_cast,
  apply filter.tendsto_at_top_mono log_succ_le_succ_card_primes,
  rw @tendsto_nat_add _ _ (λ n, log ↑n) 1,
  exact tendsto_log_coe_nat,
end
