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
  split_ifs,
  repeat {linarith},

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
    repeat {refl},
  },
  -- Case n < i < m
  by_cases i_btwn_n_m : n < i ∧ i < m,
  {
    sorry
  },
  -- Case i = m
  by_cases i_eq_m : i = m,
  {
    sorry
  },
  -- Case m < i
  by_cases i_gt_m : i > m,
  {
    sorry
  },
  -- The above cases are exhaustive, leaving a contradiction at this point:
  sorry,
end

--variables (f : (simplex n) → ℝ) (h : continuous f)
