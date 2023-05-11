import topology.metric_space.basic
import topology.algebra.uniform_group
import topology.algebra.uniform_mul_action
import topology.algebra.ring.basic
import topology.algebra.star
import topology.algebra.order.field
import ring_theory.subring.basic
import group_theory.archimedean
import algebra.order.group.bounds
import algebra.periodic
import topology.instances.int

import tactic

noncomputable theory
open classical filter int metric set topological_space
open_locale classical topology filter uniformity interval
open_locale big_operators
open finset

variable n : ℕ 

example (ι : Type*) (X : ι → Type*) (T_X : Π i, topological_space $ X i) :
  (Pi.topological_space : topological_space (Π i, X i)) = ⨅ i, topological_space.induced (λ x, x i) (T_X i) :=
rfl

-- Define ℝⁿ as a subtype of ℕ → ℝ
--  in order to inherit subtype topology
def R (n : ℕ) : Type := { f : ℕ → ℝ // ∀ i : ℕ, i > n → f i = 0 }

instance : topological_space (R n) := subtype.topological_space

-- Define simplices as a subtype of ℕ → ℝ
--   inherit subtype topology
--   and coerce it as a subtype of ℝⁿ
def simplex (n : ℕ) : Type := 
{f : ℕ → ℝ // ∑ j in finset.range (n+1), f j = 1 ∧ ∀ i : ℕ, (i > n → f i = 0) ∧ f i ≥ 0}

instance : topological_space (simplex n) := subtype.topological_space

instance : has_coe (simplex n) (R n) :=
⟨λ x, ⟨x.val, 
begin
  intros i hi,
  exact (x.property.right i).left hi,
end⟩⟩

-- Shift functions on sequences and associated theorems
--

variable f : ℕ → ℝ
variable m : ℕ

-- Shifting a sequence at position n, corresponds to
-- inserting a 0 into the sequence so that it's in the
-- nᵗʰ position
def shift (n : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := 
λ i, if i < n then f i else if n = i then 0 else f (i-1)

lemma composition_relation_for_shifts {m n : ℕ} : n < m → shift(n) ∘ shift(m) = shift(m+1) ∘ shift(n) :=
begin
  intros n_lt_m,
  ext f i,
  repeat {rw function.comp_app},
  unfold shift,
  --repeat {linarith},
  -- Case i < n
  by_cases i_lt_n : i < n,
  {
    -- some helper propositions to encourage `split_ifs` 
    -- into making the appropriate simplifications:
    have i_lt_m : i < m, by linarith,
    have i_lt_mp1 : i < m+1, by linarith,

    split_ifs,
    refl,
  },
  -- Case i = n
  by_cases i_eq_n : i = n,
  {
    -- some helper propositions to encourage `split_ifs` 
    -- into making the appropriate simplifications:
    have i_lt_m : i < m, by linarith,
    have i_lt_mp1 : i < m+1, by linarith,
    have n_eq_i: n = i := by { rw i_eq_n, }, -- this one looks odd but is seemingly necessary

    split_ifs,
    refl,
  },
  -- We now have i > n (there must be a better proof than this mess!)
  have i_gt_n : i > n, by {
    have i_neq_n : i ≠ n := by { exact i_eq_n, },
    --have n_neq_i : n ≠ i := by { exact ne.symm i_neq_n, },
    push_neg at i_lt_n,
    have i_ge_n : i ≥ n := by { rw ge_iff_le, exact i_lt_n, },
    exact lt_of_le_of_ne i_ge_n i_neq_n.symm,
  },
  -- Case n < i < m
  by_cases i_lt_m : i < m,
  {
    have i_lt_mp1 : i < m+1, by linarith,
    have i_neq_n : i ≠ n := by linarith,
    have n_neq_n : n ≠ i := by { exact ne.symm i_neq_n, },
    split_ifs,
    refl,
    have i_lt_im1 : i < i-1 := by {
       calc i < m : i_lt_m
       ... = i - 1 : by { rw h_1, },
    },
    sorry,
  },
  -- Case i = m
  by_cases i_eq_m : i = m,
  {
    sorry,
  },
  -- Case m < i
  by_cases i_gt_m : i > m,
  {
    sorry,
  },
  -- The above cases are exhaustive, leaving a contradiction at this point:
  sorry,
end

--variables (f : (simplex n) → ℝ) (h : continuous f)
