import algebra.big_operators.intervals
import algebra.big_operators.order
import data.nat.basic
import data.nat.factorization.basic
import data.nat.factors
import data.nat.interval
import data.nat.log
import data.real.basic
import data.fintype.basic
import data.finset.basic
import data.set.intervals.basic
import order.with_bot  -- with_bot.decidable_le

open_locale big_operators

-- def is_prime_le (n p : ℕ) : Prop := p ≤ n ∧ p.prime
--
-- -- Is this necessary? Feels redundant?
-- instance decidable_is_prime_le (n p : ℕ) : decidable (is_prime_le n p) :=
-- begin
--   apply decidable_of_iff (p ≤ n ∧ p.prime),
--   rw is_prime_le,
-- end

-- Could define all_factors_le using k.factors.maximum ≤ n?
-- However, it's difficult to work with (list.maximum ≤ n).
-- Instead define with for-all statement; use list.maximum to prove decidable.
-- TODO: Consider k in ℕ+ rather than ℕ?
def all_factors_le (n k : ℕ) : Prop := ∀ (p : ℕ), p ∈ k.factors → p ≤ n

lemma all_factors_le_one (n : ℕ) : all_factors_le n 1 := by simp [all_factors_le]

lemma all_factors_le_of_le {n : ℕ} {k : ℕ} (hk : k ≤ n) : all_factors_le n k :=
begin
  rw all_factors_le,
  intros p hp,
  apply le_trans _ hk,
  exact nat.le_of_mem_factors hp,
end

-- Prove decidable.

lemma exists_maximum_eq_coe_iff {l : list ℕ} : (∃ x : ℕ, l.maximum = ↑x) ↔ l ≠ list.nil :=
begin
  apply iff.intro,
  { intro h,
    cases h with x hx,
    rw list.maximum_eq_coe_iff at hx,
    exact list.ne_nil_of_mem hx.left, },
  { intro h,
    replace h := list.foldr_max_of_ne_nil h,
    rw ← h,
    simp, },
end

-- This feels too fundamental? Doesn't exist in mathlib?
lemma maximum_le_iff_forall_le {l : list ℕ} {m : ℕ} :
  l.maximum ≤ ↑m ↔ ∀ (x : ℕ), x ∈ l → x ≤ m :=
begin
  cases decidable.em (l = list.nil),
  { rw h, simp, },
  { rw (by simp : ¬l = list.nil ↔ l ≠ list.nil) at h,
    -- Get the actual maximum.
    rw ← exists_maximum_eq_coe_iff at h,
    cases h with c hc,
    rw hc,
    simp,
    rw list.maximum_eq_coe_iff at hc,
    apply iff.intro,
    { intros h x hx,
      apply le_trans _ h,
      exact hc.right x hx, },
    { intro h,
      exact h c hc.left, }, },
end

-- These two types are equal? Why do we need to define this?
def convert (x : option ℕ) : with_bot ℕ := x

-- This feels like a more natural way to write maximum?
lemma maximum_eq_foldr {l : list ℕ} : l.maximum = list.foldr (max ∘ coe) ⊥ l :=
begin
  rw list.maximum,
  rw list.argmax,
  rw ← list.foldr_map,
  rw ← list.foldl_eq_foldr max_commutative max_associative,
  rw list.foldl_map,
  -- Need list.foldl_hom because lhs uses (option ℕ) and rhs uses (with_bot ℕ).
  have h : (∀ (x : option ℕ), x = convert x) := by { intro x, rw convert, },
  rw h (list.foldl _ none _),
  -- rw (h none : ⊥ = convert none),  -- Doesn't work like this?
  have h_none : ⊥ = convert none := h none,
  rw h_none,
  rw list.foldl_hom,
  intros x y,
  rw [convert, convert],
  simp,
  rw list.arg_aux,
  cases x,
  { trivial, },
  { simp,
    rw [option.some_eq_coe, option.some_eq_coe],
    rw ite_eq_iff,
    rw [eq_comm, max_eq_right_iff],
    rw [eq_comm, max_eq_left_iff],
    simp,
    cases lt_or_le x y with hxy hyx,
    { left, exact and.intro hxy (le_of_lt hxy), },
    { right, exact hyx, }, },
end

-- Prove using foldr instead.
lemma maximum_le_iff_forall_le' {l : list ℕ} {m : ℕ} :
  l.maximum ≤ ↑m ↔ ∀ (x : ℕ), x ∈ l → x ≤ m :=
begin
  rw maximum_eq_foldr,
  apply iff.intro,
  { induction l with a l' hl', simp,
    simp,
    intros ha h,
    exact and.intro ha (hl' h), },
  { intro h,
    rw ← list.foldr_map,
    -- Use `max_le_of_forall_le` instead of induction.
    -- (Induction might be cleaner?)
    apply list.max_le_of_forall_le _ _ _,
    intro x,
    cases x, simp,
    rw option.some_eq_coe,
    have h_inj : function.injective (coe : ℕ → option ℕ) := by
    { rw function.injective,
      simp [← option.some_eq_coe], },
    rw list.mem_map_of_injective h_inj,
    simp,
    apply h, },
end

-- Do we need to prove this?
instance all_factors_le_decidable {n k : ℕ} : decidable (all_factors_le n k) :=
begin
  rw all_factors_le,
  rw ← maximum_le_iff_forall_le,
  apply with_bot.decidable_le,
end
