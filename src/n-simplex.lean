import topology.metric_space.basic
import topology.algebra.uniform_group
import topology.algebra.uniform_mul_action
import topology.algebra.ring.basic
import topology.algebra.star
import topology.algebra.order.field
import topology.algebra.module.basic
import ring_theory.subring.basic
import group_theory.archimedean
import algebra.order.group.bounds
import algebra.big_operators.basic
import algebra.periodic
import topology.instances.int
import algebra.order.group.defs
import data.finset.basic

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

lemma shift_at_n (n : ℕ) (f : ℕ → ℝ) : shift n f n = 0 :=
begin
  unfold shift,
  split_ifs,
  linarith,
  refl,
end

lemma shift_at_gt_n (n : ℕ) (f : ℕ → ℝ) (i : ℕ) : i > n → shift n f i = f (i-1) :=
begin
  intro i_gt_n,
  unfold shift,
  split_ifs,
  linarith,
  linarith,
  refl,
end

lemma shift_at_lt_n (n : ℕ) (f : ℕ → ℝ) (i : ℕ) : i < n → shift n f i = f i :=
begin
  intro i_lt_n,
  unfold shift,
  split_ifs,
  refl,
end

lemma composition_relation_for_shifts {m n : ℕ} : n < m → shift(n) ∘ shift(m) = shift(m+1) ∘ shift(n) :=
begin
  intros n_lt_m,
  ext f i,
  repeat {rw function.comp_app},
  unfold shift,
  --split_ifs,

  -- Case i < n
  by_cases i_lt_n : i < n,
  {
    -- some helper propositions to encourage `split_ifs` 
    -- into making the appropriate simplifications:
    have i_lt_m : i < m, by linarith,
    have i_lt_mp1 : i < m+1, by linarith,

    --repeat {rw function.comp_app},
    --unfold shift,
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

    --repeat {rw function.comp_app},
    --unfold shift,
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
  --  `split_ifs, repeat {refl},` will actually work but feels dirty to prove
  --  the current goal from a logical contradiction.

  -- There might be a tactic for dealing with goals following from strict orders,
  -- but until it's found, here's something that works:

  exfalso, clear f, -- remove irrelevant goals and hypotheses
  rw not_lt at i_lt_n i_gt_m,
  rw ← ne.def at i_eq_n i_eq_m,
  exact i_btwn_n_m ⟨lt_of_le_of_ne' i_lt_n i_eq_n, lt_of_le_of_ne' i_gt_m i_eq_m.symm⟩, 
end

instance (n : ℕ) : has_coe (fin n → ℝ) (ℕ → ℝ) :=
{ coe := λ x k, if h : k < n then x ⟨k, h⟩ else 0 }

lemma coe_add {n : ℕ} (x y : fin n → ℝ) : (↑(x + y) : ℕ → ℝ) = ↑x + ↑y :=
begin
  show (λ k, if h : k < n then (x + y) ⟨k, h⟩ else 0) =
    (λ k, if h : k < n then x ⟨k, h⟩ else 0) + (λ k, if h : k < n then y ⟨k, h⟩ else 0),
  nth_rewrite_rhs 0 [pi.add_def],
  ext,
  split_ifs,
  { refl },
  { rw add_zero },
end

lemma coe_smul {n : ℕ} (r : ℝ) (x : fin n → ℝ) : (↑(r • x) : ℕ → ℝ) = r • ↑x :=
begin
  show (λ k, if h : k < n then (r • x) ⟨k, h⟩ else 0) = 
    r • (λ k, if h : k < n then x ⟨k, h⟩ else 0),
  nth_rewrite_rhs 0 [pi.smul_def],
  ext,
  split_ifs,
  { refl },
  { rw smul_zero },
end

lemma shift_add (k : ℕ) (x y : ℕ → ℝ) : shift k (x + y) = shift k x + shift k y :=
begin
  unfold shift,
  nth_rewrite_rhs 0 pi.add_def,
  ext i,
  split_ifs,
  { refl },
  { rw add_zero },
  { refl },
end

lemma shift_smul (k : ℕ) (r : ℝ) (x : ℕ → ℝ) : shift k (r • x) = r • shift k x :=
begin
  unfold shift,
  nth_rewrite_rhs 0 pi.smul_def,
  ext i,
  split_ifs,
  { refl },
  { rw smul_zero },
  { refl },
end

def shift_lin (n k : ℕ) : (fin n → ℝ) →ₗ[ℝ] (fin n.succ → ℝ) :=
{ to_fun := λ x i, shift k x i,
  map_add' := λ x y, by { rw [coe_add, shift_add], refl },
  map_smul' := λ r x, by { rw [coe_smul, shift_smul], refl } }


-- Definition of some Topological maps associated to simplices
--

def face_inclusion (n: ℕ) (k: ℕ) (h: k ≤ n): simplex (n) → simplex (n+1) :=
begin
  intro face_pnt,
  set g := shift k face_pnt.val with hg, -- sequence defining corresponding point in \Delta_n
  unfold simplex,
  have h1: ∑ (j : ℕ) in finset.range (n + 2), g j = 1,
  {
    have hf := face_pnt.property.left,
    --rw hg,
    set s_k := finset.range (k+1) with hs_k,
    set s_kc := finset.range (n+2) \ s_k with hs_kc,
    -- unfold shift,
    have h2: disjoint s_k s_kc,
    {
      rw finset.disjoint_iff_inter_eq_empty,
      rw hs_kc,
      simp,
    },
    have h3: finset.range (n+2) = s_k.disj_union s_kc h2,
    {
      rw finset.disj_union_eq_union,
      rw hs_kc,
      simp,
      linarith,
    },
    rw h3,
    rw finset.sum_disj_union (h2 ),
    rw finset.sum_range_succ,
    have h4: g k = 0,
    {
      exact shift_at_n k face_pnt.val,
    },
    rw h4,
    rw add_zero,
    set s_km1 := finset.range k with hs_km1,
    set s_kmc := finset.range (n+2) \ s_km1 with hs_kmc,
    have h5: finset.sum s_kc (λ (x : ℕ), g x) = finset.sum s_kmc (λ (x : ℕ), face_pnt.val x),
    {
      sorry,
    },
    sorry,
  },
  have h2: ∀ (i : ℕ), (i > n+1 → g i = 0) ∧ g i ≥ 0,
  {
    intro i,
    split,
    {
      rw hg,
      unfold shift,
      split_ifs,
      {
        intro i_gt_n1,
        have hf := (face_pnt.property.right (i)).left,
        apply hf,
        linarith,
      },
      {
        intro irrelevant,
        refl,
      },
      {
        intro i_gt_n1,     
        have hf := (face_pnt.property.right (i-1)).left,
        apply hf,
        clear h_2 h_1 hg hf h1 g face_pnt h k,
        sorry, -- should be a theorem about this
      },
    },
    {
      clear h1,
      rw hg,
      unfold shift,
      split_ifs,
      {
        exact (face_pnt.property.right i).right,
      },
      {
        simp,
      },
      {
        exact (face_pnt.property.right (i-1)).right,
      },
   },
  },
  exact ⟨g, ⟨h1, h2⟩⟩,
end


#check continuous.cod_restrict
#check set.cod_restrict
#check continuous_map.restrict
#check continuous_subtype_val

lemma face_inclusion_continuous (n: ℕ) (k: ℕ) (h: k ≤ n): continuous (face_inclusion n k h) :=
begin
  haveI : has_continuous_smul ℝ (Π i : fin n.succ, ℝ) := 
    @pi.has_continuous_smul ℝ _ (fin n.succ) (λ i, ℝ) _ _ (λ i, by apply_instance),
  have cont: continuous (shift_lin n k) := linear_map.continuous_on_pi _,
  -- have : continuous (shift_lin n k ∘ (subtype.val : simplex n → (fin n → ℝ))) := by simp, 

  sorry,
end

lemma face_inclusion_injective (n: ℕ) (k: ℕ) (h: k ≤ n): function.injective (face_inclusion n k h) :=
begin
  unfold function.injective,
  intros x₁ x₂,
  intro h2,
  ext i,
  by_cases h3: i ≥ k,
  {
    calc x₁.val i = shift k x₁.val (i+1) : _
    ...           = (face_inclusion n k h x₁).val (i+1) : _
    ...           = (face_inclusion n k h x₂).val (i+1) : by sorry
    ...           = shift k x₂.val (i+1) : _
    ...           = x₂.val i : _,
    {
      unfold shift,
      split_ifs,
      {
        exfalso,
        clear h2 h x₁ x₂ n,
        rw ← not_le at h_1,
        have h4 : i+1 ≥ k, by linarith,
        exact h_1 h4,
      },
      {
        exfalso,
        -- contradiction between h3 and h_2
        clear h2 h x₁ x₂ n h_1,
        rw ge_iff_le at h3,
        rw ← not_lt at h3,
        have i_lt_k: i < k, by linarith,
        exact h3 i_lt_k,
      },
      {
        -- only need i and x₁
        clear h_2 h_1 h3 h2 h x₂,
        simp,
      },
    },
    {
      unfold shift,
      split_ifs,
      {
        exfalso,
        clear h2 h x₁ x₂ n,
        rw ← not_le at h_1,
        have h4 : i+1 ≥ k, by linarith,
        exact h_1 h4,
      },
      {
        exfalso,
        clear h_1 h2 x₁ x₂ h n,
        rw ge_iff_le at h3,
        rw ← not_lt at h3,
        have h4: k > i, by linarith,
        exact h3 h4,
      },
      {
        have h4: i + 1 > k, by linarith,
        clear h_1 h_2,
        unfold face_inclusion,
        have goal := shift_at_gt_n (k) x₁.val (i+1) h4,
        rw ← goal,
        simp,
      },
    },
    {
      unfold face_inclusion,
      refl,
    },
    {
      have i1_gt_k: i+1 > k := by linarith,
      unfold shift,
      split_ifs,
      {
        exfalso,
        clear h3 h2 h x₁ x₂ n,
        exact not_lt.2 (le_of_lt h_1) i1_gt_k,
      },
      {
        exfalso,
        clear h2 h_1 h3 x₁ x₂ h n,
        exact ne_of_lt i1_gt_k h_2,
      },
      {
        clear h_2 h_1 h3 h2 x₁ h i1_gt_k,
        simp,
      },
    },
  },
  rw not_le at h3,
  calc x₁.val i = shift k x₁.val (i) : by sorry
  ...           = (face_inclusion n k h x₁).val (i) : by sorry
  ...           = (face_inclusion n k h x₂).val (i) : by sorry
  ...           = shift k x₂.val (i) : by sorry
  ...           = x₂.val i : by sorry,
end
