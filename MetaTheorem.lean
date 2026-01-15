import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Meta-Theorem: Product Metric Optimality

## The Core Insight

For products of cyclic groups under the **product metric** (sum of circular
distances on each factor), simple coordinate reflections always achieve
optimal pairing cost. This is because generators have disjoint supports,
making cost additive under composition.

**Important**: The product metric on a CRT decomposition Z_{n₁} × ⋯ × Z_{nₖ}
is NOT the same as the native circular metric on Zₙ. The CRT is a group
isomorphism, not an isometry. The optimality results here concern the
product metric only.

## Product Structure (Simple = Optimal under Product Metric)

When the space has:
1. Space = S₁ × S₂ × ⋯ × Sₙ (product of cyclic groups)
2. Distance = d₁ + d₂ + ⋯ + dₙ (product metric, i.e., ℓ¹ on the product)
3. Each generator negates ONE component

Then:
  cost(composite) = cost(gen₁) + cost(gen₂) + ⋯
  min(simple) ≤ any single term ≤ sum = composite cost

## Coupled Structure (Composites Can Win)

On {0,1}ⁿ with Hamming distance, generators (complement, reversal)
act on ALL bits simultaneously, so cost additivity fails and
composites CAN beat simple reflections.

## Mathematical Statement
-/

namespace MetaTheorem

/-! ## Core Abstractions -/

/-- Typeclass for group actions with additive cost.
    When generators have disjoint supports, costs are additive. -/
class AdditiveActionCost (G : Type*) (X : Type*) [Mul G] where
  /-- Cost of applying group element g at point x -/
  cost : G → X → ℕ
  /-- Costs are additive under composition -/
  cost_mul : ∀ g₁ g₂ x, cost (g₁ * g₂) x = cost g₁ x + cost g₂ x

/-! ## The Core Lemma: Minimum ≤ Sum -/

/-- For any finite collection of natural numbers, the minimum is ≤ the sum.
    This is the key lemma that makes "simple = optimal" trivial. -/
lemma min_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℕ) :
    (Finset.univ.inf' Finset.univ_nonempty f) ≤ Finset.univ.sum f := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  calc Finset.univ.inf' Finset.univ_nonempty f
      = f i := hi
    _ ≤ Finset.univ.sum f :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Variant: min of a list ≤ sum, stated with explicit minimum. -/
lemma min_of_three_le_sum (a b c : ℕ) : min a (min b c) ≤ a + b + c := by omega

/-- Variant: min ≤ any pairwise sum. -/
lemma min_le_pairwise_sum (a b c : ℕ) :
    min a (min b c) ≤ min (a + b) (min (a + c) (min (b + c) (a + b + c))) := by omega

/-! ## The Additivity Principle -/

/-- **Core Theorem**: If composite cost = sum of component costs,
    then min(simple) ≤ composite cost.

    This is now a one-liner using min_le_sum! -/
theorem simple_beats_composite_when_additive {ι : Type*} [Fintype ι] [Nonempty ι]
    (simpleCosts : ι → ℕ) (compositeCost : ℕ)
    (h_additive : compositeCost = Finset.univ.sum simpleCosts) :
    Finset.univ.inf' Finset.univ_nonempty simpleCosts ≤ compositeCost := by
  rw [h_additive]; exact min_le_sum simpleCosts

/-- Existential version for backwards compatibility. -/
theorem simple_beats_composite_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (simpleCosts : ι → ℕ) (compositeCost : ℕ)
    (h_additive : compositeCost = Finset.univ.sum simpleCosts) :
    ∃ i : ι, simpleCosts i ≤ compositeCost := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty simpleCosts
  exact ⟨i, hi ▸ simple_beats_composite_when_additive simpleCosts compositeCost h_additive⟩

/-- **Main Theorem**: Under the product metric, min(simple) ≤ any composite.
    Applies to cyclic products when generators have disjoint supports. -/
theorem product_calendar_simple_optimal {ι : Type*} [Fintype ι] [Nonempty ι]
    (simpleCosts : ι → ℕ) (compositeCost : ℕ)
    (h_additive : compositeCost = Finset.univ.sum simpleCosts) :
    ∃ i : ι, simpleCosts i ≤ compositeCost :=
  simple_beats_composite_exists simpleCosts compositeCost h_additive

/-! ## Why I Ching Fails This -/

/-- The I Ching violates additivity because Hamming distance doesn't decompose.

    For hexagram h with components (b₀, b₁, b₂, b₃, b₄, b₅):
    - complement(h) = (1-b₀, 1-b₁, ..., 1-b₅) → Hamming = 6 always
    - reverse(h) = (b₅, b₄, b₃, b₂, b₁, b₀) → Hamming = #{i : bᵢ ≠ b₅₋ᵢ}
    - comp∘rev(h) = (1-b₅, 1-b₄, ..., 1-b₀)

    The key: Hamming(h, comp∘rev(h)) ≠ Hamming(h, comp(h)) + Hamming(h, rev(h))

    In fact, it can be LESS! This is why CR can beat both C and R.
-/
example : True := trivial  -- Documentation only

/-! ## Classification by Structure Type -/

/-- Structural classification of systems.
    "Product" = coordinate-local generators, optimality holds under product metric.
    "Coupled" = global generators, composites can outperform under native metric. -/
inductive CalendarType
  | Product     -- Tzolkin, Calendar Round, Sexagenary (simple = optimal under product metric)
  | Coupled     -- I Ching, Bagua (composites can win under Hamming)

/-- Summary of structural and optimality findings.
    Note: for Product systems, "simple = optimal" is under the product metric
    on the CRT decomposition, NOT the native circular metric on Zₙ.
    The fiber product structure (locked components) is metric-independent. -/
def classification : List (String × CalendarType × String) :=
  [ ("Tzolkin",        .Product, "Z₁₃ × Z₂₀ with product metric"),
    ("Calendar Round", .Product, "Z₄ × Z₅ × Z₁₃ × Z₇₃ with product metric (Z₅ locked)"),
    ("Sexagenary",     .Product, "Z₅ × Z₄ × Z₃ with product metric (Z₂ locked via Z₄)"),
    ("I Ching",        .Coupled, "{0,1}⁶ with Hamming distance"),
    ("Bagua",          .Coupled, "{0,1}³ with Hamming distance") ]

end MetaTheorem
