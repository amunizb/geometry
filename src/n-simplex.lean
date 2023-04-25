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

noncomputable theory
open classical filter int metric set topological_space
open_locale classical topology filter uniformity interval

--universes u v w
--variables {α : Type u} {β : Type v} {γ : Type w}
--instance : noncompact_space ℝ := int.closed_embedding_coe_real.noncompact_space

-- define ℝ^n as a topological space
def R_n : Type := {f : ℕ → ℝ | ∃ n : ℕ, ∀ i : ℕ, i > n → f i = 0}

def simplex_n : Type := {f : ℕ → ℝ | ∃ n : ℕ, ∀ i : ℕ, i > n → f i = 0 ∧ f i ≥ 0 ∧ ∑ j in finset.range (i+1), f j = 1}





