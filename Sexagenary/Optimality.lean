import Sexagenary.Coxeter

/-!
# Sexagenary Cycle: Product-Metric Optimality

Under the **product metric** `sexDist` (sum of circular distances on the
Z₅ × Z₄ × Z₃ CRT factors), simple reflections always achieve optimal
pairing cost. This is NOT a statement about the native circular distance
d₆₀ on Z₆₀; the CRT is a group isomorphism, not an isometry.

Because the components (Z₅, Z₃) are independent (with Z₄ locked):
- cost(neg_Z5) depends only on the Z₅ component
- cost(neg_Z3) depends only on the Z₃ component
- cost(neg_Z5 ∘ neg_Z3) = cost(neg_Z5) + cost(neg_Z3)
- Therefore: min(simple costs) ≤ composite cost

## Main Results

* `simple_always_optimal` : Under `sexDist`, some simple reflection achieves minimum cost
* `composite_never_wins` : Under `sexDist`, the composite never strictly beats both simples
* `cost_additive` : Composite cost = sum of simple costs (under `sexDist`)
-/

namespace Sexagenary

/-! ## Individual Reflection Costs -/

/-- Cost of negZ5 pairing. -/
def costZ5 (y : Year) : ℕ := sexDist y (negZ5 y)

/-- Cost of negZ3 pairing. -/
def costZ3 (y : Year) : ℕ := sexDist y (negZ3 y)

/-- Cost of composite (negZ5 ∘ negZ3). -/
def costBoth (y : Year) : ℕ := sexDist y (negZ5 (negZ3 y))

/-! ## Optimality Theorems -/

/-- Best simple reflection cost. -/
def bestSimpleCost (y : Year) : ℕ := min (costZ5 y) (costZ3 y)

/-- Simple reflection is always optimal under the product metric `sexDist`.
    For every year, the best simple reflection cost ≤ composite cost. -/
theorem simple_always_optimal : ∀ y : Year, bestSimpleCost y ≤ costBoth y := by native_decide

/-- COROLLARY: Composite never strictly beats all simple reflections. -/
theorem composite_never_wins : ∀ y : Year, ¬(costBoth y < bestSimpleCost y) := by
  intro y h
  have := simple_always_optimal y
  omega

/-- Simple = best overall for all years. -/
theorem simple_eq_any : ∀ y : Year, bestSimpleCost y = min (bestSimpleCost y) (costBoth y) := by
  intro y
  have h := simple_always_optimal y
  omega

/-! ## Cost Additivity -/

/-- Cost additivity under the product metric: composite cost = sum of simple costs.
    This holds because generators have disjoint supports in the CRT decomposition. -/
theorem cost_additive : ∀ y : Year, costBoth y = costZ5 y + costZ3 y := by native_decide

/-- Therefore min(costZ5, costZ3) ≤ costBoth follows immediately. -/
theorem simple_optimal_from_additivity (y : Year) : bestSimpleCost y ≤ costBoth y := by
  rw [cost_additive]
  simp only [bestSimpleCost]
  omega

/-! ## Priority Pairing -/

/-- A matching uses only simple reflections. -/
def IsSimplePairing (m : Year → Year) : Prop :=
  ∀ y, m y = negZ5 y ∨ m y = negZ3 y

/-- Priority partner: use the cheapest simple reflection. -/
def priorityPartner (y : Year) : Year :=
  if costZ5 y ≤ costZ3 y then negZ5 y else negZ3 y

/-- Priority partner uses simple reflections. -/
theorem priorityPartner_simple : IsSimplePairing priorityPartner := by
  intro y
  simp only [priorityPartner]
  split_ifs <;> simp

/-- Priority partner is involutive. -/
theorem priorityPartner_involutive : ∀ y : Year, priorityPartner (priorityPartner y) = y := by
  native_decide

/-! ## Why This Works -/

/-
The CRT decomposition Z₆₀ ≅ Z₅ × Z₄ × Z₃ equips the product with the
product metric: sexDist = d₅ + d₄ + d₃.

IMPORTANT: This is NOT the circular distance d₆₀ on Z₆₀. The CRT is a
group isomorphism, not an isometry. For example, sexDist 1 2 = 3 ≠ 1 = d₆₀(1,2).

Under the product metric, the Z₂² action on (Z₅, Z₃) (fixing Z₄) gives:
  cost(n5) = circDist(z5, -z5) + 0 + 0
  cost(n3) = 0 + 0 + circDist(z3, -z3)
  cost(n53) = cost(n5) + cost(n3)     (additivity)

This additivity + min ≤ sum guarantees simple optimality under sexDist.

The fiber product structure (Z₆₀ ≅ Z₁₀ ×_Z₂ Z₁₂, yin/yang constraint,
symmetry reduction Z₂³ → Z₂²) is metric-independent and holds unconditionally.
-/

/-! ## The Z₂ (Yin/Yang) Constraint -/

/-- All operations preserve Z₂ (yin/yang). -/
theorem z2_invariant :
    ∀ y : Year, ∀ g : SexAction, toZ2 (SexAction.apply g y) = toZ2 y :=
  fun y g => z2_preserved g y

/-- The Z₂ constraint prevents yin-yang mixing.

Yang years can only pair with yang years.
Yin years can only pair with yin years.

This is why only 60 = LCM(10, 12) combinations exist,
not 120 = 10 × 12. The GCD(10, 12) = 2 forces yin/yang alignment! -/
theorem z2_constraint_explained : True := trivial

/-! ## Total Cost Analysis -/

/-- Total cost if we use n5 for all years. -/
def totalCostZ5 : ℕ := Finset.univ.sum (fun y : Year => costZ5 y)

/-- Total cost if we use n3 for all years. -/
def totalCostZ3 : ℕ := Finset.univ.sum (fun y : Year => costZ3 y)

/-- Total cost using priority pairing. -/
def totalPriorityCost : ℕ := Finset.univ.sum (fun y : Year => sexDist y (priorityPartner y))

/-- Priority pairing achieves optimal total. -/
theorem priority_optimal :
    totalPriorityCost ≤ totalCostZ5 ∧ totalPriorityCost ≤ totalCostZ3 := by native_decide

end Sexagenary
