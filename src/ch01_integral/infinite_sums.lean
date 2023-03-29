import data.real.basic
import data.real.nnreal
import data.real.ennreal
import data.pnat.factors
import data.pnat.prime
import data.finset.basic
import data.finset.pointwise
import data.multiset.basic
import data.multiset.fintype
import data.multiset.bind
import order.filter.basic
import order.filter.at_top_bot
import group_theory.submonoid.membership
import analysis.specific_limits.basic
import topology.basic
import topology.algebra.infinite_sum
import topology.instances.ennreal
import logic.equiv.defs
import algebra.group.basic  -- inv_inj
import algebra.group_power.basic  -- inv_pow
import algebra.big_operators.basic  -- finset.prod_inv_distrib

import .factors_le

open real filter
open_locale big_operators

variables {n : ℕ}

def primes_le (n : ℕ) : finset nat.primes := (finset.range (n+1)).subtype nat.prime 

-- def all_factors_le (n k : ℕ) : Prop := ∀ (p : ℕ), p ∈ k.factors → p ≤ n


-- Define (commutative) submonoid of pnat using only primes_le n (closed under mul).
-- Later: Establish equivalence of (pnat_fac_le n) and finset.pi (for prod_sum).
def pnat_fac_le (n : ℕ) : submonoid ℕ+ := {
  carrier := {x : ℕ+ | all_factors_le n ↑x},  -- Doesn't need decidable?
  mul_mem' := by {
    simp [all_factors_le],
    intros a b ha hb p,
    specialize ha p,
    specialize hb p,
    rw nat.mem_factors_mul (ne_zero_of_lt a.prop) (ne_zero_of_lt b.prop),
    intro hp,
    exact or.elim hp ha hb, },
  one_mem' := by { simp [all_factors_le], },
}


namespace pnat_fac_le

instance ordered_comm_monoid : _root_.ordered_comm_monoid ↥(pnat_fac_le n) :=
  submonoid.to_ordered_comm_monoid _

instance has_one_pnat_fac_le : has_one (pnat_fac_le n) :=
{ one := ⟨1, show all_factors_le n (1 : ℕ+), by simp [all_factors_le]⟩, }

-- Necessary to define this? Seems to be needed below.
-- (`prime_multiset` is defined equal to `multiset nat.primes`)
instance has_mem_prime_multiset : has_mem nat.primes prime_multiset := { mem := multiset.mem, }

-- Switch to/from `nat.factors` representation (more results available?).
lemma mem_factor_multiset_iff {x : ℕ+} {p : nat.primes} :
  p ∈ pnat.factor_multiset x ↔ ↑p ∈ nat.factors ↑x :=
begin
  simp [pnat.factor_multiset, prime_multiset.of_nat_list, prime_multiset.of_nat_multiset],
  apply iff.intro,
  { intro h, cases h with q hq, cases hq with hq hq', simp [← hq'], exact hq, },
  { cases p with p hp, simp, },
end

-- Need to add has_mem to prime_multiset for this?
lemma mem_primes_le_of_mem_factor_multiset {x : pnat_fac_le n} {p : nat.primes} :
  p ∈ pnat.factor_multiset ↑x → p ∈ primes_le n :=
begin
  cases x with x hx,
  cases x with x hx',
  simp,
  intro hp,
  simp [pnat_fac_le, ← submonoid.mem_carrier, all_factors_le] at hx,
  simp [mem_factor_multiset_iff] at hp,
  specialize hx p hp,
  simp [primes_le, nat.lt_succ_iff],
  exact hx,
end

-- Is use of attach here neat? Or does it make things messier later?
def factor_multiset (x : pnat_fac_le n) : multiset ↥(primes_le n) :=
  (pnat.factor_multiset ↑x).attach.map
  (λ p, ⟨p.val, (mem_primes_le_of_mem_factor_multiset p.property)⟩)

end pnat_fac_le


namespace primes_le

lemma mem_pnat_fac_le_of_mem_primes_le {p : nat.primes} : p ∈ primes_le n → ↑p ∈ pnat_fac_le n :=
begin
  simp [primes_le, nat.lt_succ_iff],
  simp [pnat_fac_le, all_factors_le],
  cases p with p hp,
  simp [← coe_coe],
  simp [nat.factors_prime hp],
end

-- Enable cast from (primes_le n) to (pnat_fac_le n).
instance has_coe_pnat_fac_le : has_coe ↥(primes_le n) (pnat_fac_le n) :=
{ coe := λ p, ⟨↑(p.val), mem_pnat_fac_le_of_mem_primes_le p.property⟩, }

instance has_coe_multiset_pnat_fac_le : has_coe (multiset ↥(primes_le n)) (multiset (pnat_fac_le n)) :=
{ coe := λ s, s.map coe, }

instance has_coe_prime_multiset : has_coe (multiset ↥(primes_le n)) prime_multiset :=
{ coe := λ s, s.map coe, }

lemma injective_coe_prime_multiset : function.injective (coe : multiset ↥(primes_le n) → prime_multiset) :=
begin
  intros a b,
  unfold_coes,
  rw multiset.map_eq_map, { cc, },
  simp,
  exact subtype.coe_injective,
end

def multiset_prod : multiset ↥(primes_le n) → pnat_fac_le n := λ s, multiset.prod ↑s

end primes_le


namespace pnat_fac_le

-- lemma prod_factors_eq_self' (x : ↥(pnat_fac_le n)) : ↑(multiset_prod (factor_multiset x)) = (↑x : ℕ+) :=
-- begin
--   simp [multiset_prod, factor_multiset],
--   unfold_coes,
--   simp,
--   rw (_ : (λ u, ⟨↑↑u, _⟩ : {a // a ∈ pnat.factor_multiset ↑x} → ℕ+) = (coe : nat.primes → ℕ+) ∘ coe),
--   rotate, { ext, norm_cast, },
--   simp,
--   have h := pnat.prod_factor_multiset ↑x,
--   rw prime_multiset.prod at h,
--   unfold_coes at h,
--   simp [prime_multiset.to_pnat_multiset] at h,
--   exact h,
-- end

lemma prod_factors_eq_self (x : ↥(pnat_fac_le n)) :
  primes_le.multiset_prod (pnat_fac_le.factor_multiset x) = x :=
begin
  -- Easier to work with ℕ+?
  rw ← subtype.coe_inj,
  simp [primes_le.multiset_prod, pnat_fac_le.factor_multiset],
  unfold_coes,
  simp,
  rw (_ : (λ u, ⟨↑↑u, _⟩ : {a // a ∈ pnat.factor_multiset ↑x} → ℕ+) = (coe : nat.primes → ℕ+) ∘ coe),
  rotate, { ext, norm_cast, },
  simp,
  have h := pnat.prod_factor_multiset ↑x,
  rw prime_multiset.prod at h,
  unfold_coes at h,
  simp [prime_multiset.to_pnat_multiset] at h,
  exact h,
end

lemma factor_prod_primes_eq_self (s : multiset ↥(primes_le n)) : pnat_fac_le.factor_multiset (primes_le.multiset_prod s) = s :=
begin
  -- Easier to work with prime_multiset?
  rw ← primes_le.injective_coe_prime_multiset.eq_iff,
  simp [primes_le.multiset_prod, pnat_fac_le.factor_multiset],
  unfold_coes,
  simp,
  rw multiset.attach_map_coe,
  rw (_ : ↑((↑s : multiset ↥(pnat_fac_le n)).prod) = (s : prime_multiset).prod),
  { rw prime_multiset.factor_multiset_prod, unfold_coes, },
  { push_cast,
    unfold_coes,
    simp,
    rw (_ : (λ (x : ↥(primes_le n)), (⟨(↑(↑x : nat.primes) : ℕ), _⟩ : ℕ+)) = (coe : ↥(primes_le n) → ℕ+)),
    rotate, { unfold_coes, },
    rw prime_multiset.prod,
    rw (_ : ↑(multiset.map coe s) = (multiset.map coe s)),
    unfold_coes,
    simp [prime_multiset.to_pnat_multiset],
    apply multiset.map_congr rfl,
    intros p hp,
    unfold_coes, },
end

def equiv_multiset : pnat_fac_le n ≃ multiset (primes_le n) :=
{ to_fun    := pnat_fac_le.factor_multiset,
  inv_fun   := primes_le.multiset_prod,
  left_inv  := prod_factors_eq_self,
  right_inv := factor_prod_primes_eq_self, }

end pnat_fac_le


-- Another trivial coe...
instance multiset_primes_le_has_coe : has_coe (multiset (primes_le n)) prime_multiset :=
{ coe := λ s, s.map coe }


/- Show equivalence between (with_pnat_fac_le n) and finset.pi so that we can equate to geometric sum. -/

def multiset_to_finset_pi {α : Type*} [decidable_eq α] {s : finset α}
  (f : multiset ↥s) : Π (x : α), x ∈ s → ℕ := λ x hx, f.count ⟨x, hx⟩

def finset_pi_to_multiset {α : Type*} {s : finset α}
  (f : Π (x : α), x ∈ s → ℕ) : multiset ↥s :=
  (finset.univ : finset ↥s).val.bind (λ x, multiset.replicate (f x.val x.property) x)

lemma pi_to_multiset_to_pi {α : Type*} [decidable_eq α] {s : finset α} (f : multiset ↥s) :
  finset_pi_to_multiset (multiset_to_finset_pi f) = f :=
begin
  simp [multiset_to_finset_pi, finset_pi_to_multiset],
  ext x,
  rw multiset.count_bind,
  simp_rw multiset.count_replicate,
  rw ← finset.attach_val,
  rw ← finset.sum,  -- finset.sum f s = multiset.sum (multiset.map f s.val)
  rw finset.sum_ite_eq,
  simp [ite_eq_left_iff],
end

lemma multiset_to_pi_to_multiset {α : Type*} [decidable_eq α] {s : finset α} (f : Π (x : α), x ∈ s → ℕ) :
  multiset_to_finset_pi (finset_pi_to_multiset f) = f :=
begin
  simp [multiset_to_finset_pi, finset_pi_to_multiset],
  ext x hx,
  simp [multiset.count_bind, multiset.count_replicate],
  rw ← finset.attach_val,
  rw ← finset.sum,  -- finset.sum f s = multiset.sum (multiset.map f s.val)
  rw finset.sum_ite_eq,
  rw ite_eq_left_iff.mpr, { simp, },
  intro h, exfalso, apply h,
  exact finset.mem_attach _ _,
end

def equiv_multiset_finset_pi {α : Type*} [decidable_eq α] {s : finset α} :
  multiset ↥s ≃ (Π (x : α), x ∈ s → ℕ) :=
{ to_fun    := multiset_to_finset_pi,
  inv_fun   := finset_pi_to_multiset,
  left_inv  := pi_to_multiset_to_pi,
  right_inv := multiset_to_pi_to_multiset, }

def equiv_pnat_fac_le_finset_pi : pnat_fac_le n ≃ (Π (p : nat.primes), p ∈ primes_le n → ℕ) :=
  equiv.trans pnat_fac_le.equiv_multiset equiv_multiset_finset_pi


def finset_pi_range (n : ℕ) : ℕ → finset (Π (p : nat.primes), p ∈ primes_le n → ℕ) :=
  λ m, (primes_le n).pi (λ (p : nat.primes), finset.range m)

lemma mono_finset_pi_range : monotone (finset_pi_range n) :=
begin
  rw monotone,
  intros a b h,
  simp [finset_pi_range],
  apply finset.pi_subset,
  intros p hp,
  -- mono,  -- no good match found
  exact finset.range_mono h,
end

-- Make use of the fact that (⊥ : ℕ) = 0.
def pi_sup (f : Π (p : nat.primes), p ∈ primes_le n → ℕ) : ℕ :=
  finset.sup (primes_le n).attach (λ p, f p.val p.property : ↥(primes_le n) → ℕ)

lemma primes_le_nonempty (h : 2 ≤ n) : (primes_le n).nonempty :=
begin
  rw finset.nonempty,
  existsi (⟨2, nat.prime_two⟩ : nat.primes),
  simp [primes_le],
  linarith,
end

lemma subset_of_finset_pi_range_of_le_max {fs : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)} {m : ℕ} :
  finset.sup fs pi_sup < m → fs ⊆ finset_pi_range n m :=
begin
  intros hm,
  simp [finset_pi_range],
  intros f hf,
  simp,
  intros p hp,
  apply lt_of_le_of_lt _ hm,
  apply le_trans _ (finset.le_sup hf),
  simp [pi_sup],
  -- TODO: Some cleaner way to do this?
  have h : f p hp = (λ (q : ↥(primes_le n)), f (↑q : nat.primes) q.prop) ⟨p, hp⟩ := by simp,
  rw h, clear h,
  apply finset.le_sup,
  simp,
end

-- Can this be proven more simply? By relation to multiset or finsupp?
lemma tendsto_pi_range_at_top_at_top : tendsto (finset_pi_range n) at_top at_top :=
begin
  rw monotone.tendsto_at_top_at_top_iff mono_finset_pi_range,
  intro fs,
  existsi (finset.sup fs pi_sup).succ,
  apply subset_of_finset_pi_range_of_le_max,
  exact nat.lt_succ_self _,
end


noncomputable def prod_sum_inv_primes_le (n : ℕ) : ℕ → nnreal :=
  λ m, ∏ p in primes_le n, ∑ k in finset.range m, (↑p)⁻¹ ^ k

lemma tendsto_prod_sum_inv_prod_geom_series (n : ℕ) :
  tendsto (prod_sum_inv_primes_le n) at_top
  (nhds (∏ p in primes_le n, (1 - (↑p)⁻¹)⁻¹)) :=
begin
  apply tendsto_finset_prod,
  intros p hp,
  apply has_sum.tendsto_sum_nat,
  refine nnreal.has_sum_geometric _,
  rw inv_lt_one_iff,
  apply or.inr,
  norm_cast,
  exact nat.prime.one_lt p.prop,
end

instance has_coe_submonoid_pnat_set_nat : has_coe (submonoid ℕ+) (set ℕ) :=
{ coe := λ sm, coe '' sm.carrier, }  -- Any better way to do this? coe is injective...

lemma prod_geom_to_ennreal {s : finset nat.primes} :
  (↑(∏ p in s, (1 - (↑p : nnreal)⁻¹))⁻¹ : ennreal) = ∏ p in s, (↑(1 - (↑p : nnreal)⁻¹)⁻¹ : ennreal) :=
begin
  rw ← finset.prod_inv_distrib,
  push_cast,
end

theorem sum_inv_pnat_fac_le_eq_prod_geom_series (n : ℕ) :
  has_sum
  (λ p, (↑p)⁻¹ : ↥(pnat_fac_le n) → nnreal)
  (∏ p in primes_le n, (1 - (↑p)⁻¹)⁻¹) :=
begin
  -- Convert from sum over pnat_fac_le to sum over finset.pi.
  rw ← equiv.has_sum_iff equiv_pnat_fac_le_finset_pi.symm,
  simp [equiv_pnat_fac_le_finset_pi, equiv_multiset_finset_pi, pnat_fac_le.equiv_multiset, equiv.trans],

  -- Switch to ennreal to work with ∑' and ⨆.
  rw ← ennreal.has_sum_coe,
  simp,
  rw summable.has_sum_iff ennreal.summable,  -- Shorter version exists?
  rw ennreal.tsum_eq_supr_sum,

  have h := tendsto_prod_sum_inv_prod_geom_series n,
  rw prod_sum_inv_primes_le at h,
  simp_rw finset.prod_sum at h,

  -- Sum of nnreal will be equal to supremum over subsets.
  -- And limit over a sequence of subsets that approaches at_top will be supremum.
  -- Need to show that the limit we have gives the supremum.

  -- Change range of summation.
  -- TODO: Is there an identity for this? finset.image?
  rw (by { simp [finset_pi_range], } :
    ∀ {f : (Π (p : nat.primes), p ∈ primes_le n → ℕ) → nnreal},
    (λ (m : ℕ), ∑ ks in (primes_le n).pi (λ (a : nat.primes), finset.range m), f ks) =
    (λ (s : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)), ∑ ks in s, f ks) ∘ finset_pi_range n)
    at h,

  rw ← tendsto_iff_tendsto_subseq_of_monotone
    (_ : monotone
      (λ (s : finset (Π (p : nat.primes), p ∈ primes_le n → ℕ)),
        ∑ p in s, ∏ x in (primes_le n).attach, (↑(x.val) : nnreal)⁻¹ ^ p x.val x.property))
    tendsto_pi_range_at_top_at_top
    at h,
  rotate,
  { rw monotone,
    intros a b h',
    apply finset.sum_le_sum_of_subset,
    exact h', },

  -- Switch to ennreal (need complete_linear_order).
  rw ← ennreal.tendsto_coe at h,
  push_cast at h,  -- Move coe for supr_eq_of_tendsto.
  replace h := supr_eq_of_tendsto _ h,
  rotate,
  { rw monotone,
    intros a b h',
    norm_cast,
    apply finset.sum_le_sum_of_subset,
    exact h', },

  -- Make the RHS match.
  push_cast,
  simp_rw ← coe_coe,
  rw prod_geom_to_ennreal,
  rw ← h,
  clear h,

  apply supr_congr,
  intro s,
  apply finset.sum_congr rfl,
  intros ks hks,

  simp [primes_le.multiset_prod, finset_pi_to_multiset],
  norm_cast,
  simp,
  -- Now need to get the ennreal out from inside the ⁻¹?
  rw (by simp : ∀ {x : ℕ}, (↑x : ennreal) =  ↑(↑x : nnreal)),
  rw ← ennreal.coe_inv _,
  rotate, { simp, },
  -- Timeout with simp here.
  rw ennreal.coe_eq_coe,
  rw inv_inj,
  rw ← submonoid.coe_multiset_prod,
  rw (_ : ∀ {s : multiset ↥(primes_le n)}, (↑s : multiset ↥(pnat_fac_le n)) = multiset.map coe s),
  rotate, { unfold_coes, simp, },
  simp [multiset.map_bind],
  rw ← pnat.coe_coe_monoid_hom,  -- replace coe : ℕ+ → ℕ with ⇑pnat.coe_monoid_hom
  rw monoid_hom.map_multiset_prod, -- convert prod ℕ+ to prod ℕ
  simp [finset.prod_eq_multiset_prod],
  rw multiset.map_congr rfl,
  intros p hp,
  -- Timeout with simp here.
  repeat { rw ← coe_coe, },
end
