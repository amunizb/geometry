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

-- define ℝ^n as a topological space
def R(n) : Type := {f : ℕ → ℝ | ∀ i : ℕ, i > n-1 → f i = 0}

example : topological_space (R n) := by sorry

-- define the nth simplex as a topological space
def simplex(n) : Type := {f : ℕ → ℝ | ∀ i : ℕ, i > n → f i = 0  ∧ f i ≥ 0 ∧ ∑ j in finset.range (n+1), f j = 1 }

example : topological_space (simplex n) := by sorry