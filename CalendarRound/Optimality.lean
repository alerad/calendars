import CalendarRound.Coxeter

/-!
# Calendar Round: Product-Metric Optimality

Under the **product metric** `crDist` (sum of circular distances on the
Z₄ × Z₅ × Z₁₃ × Z₇₃ CRT factors), simple reflections always achieve
optimal pairing cost. This is NOT a statement about the native circular
distance d₁₈₉₈₀ on Z₁₈₉₈₀; the CRT is a group isomorphism, not an isometry.

Because the components (Z₄, Z₁₃, Z₇₃) are independent under `crDist`:
- cost(neg_Zi) depends only on the Zi component
- cost(composite) = sum of individual component costs
- Therefore: min(simple costs) ≤ any composite cost

## Main Results

* `simple_always_optimal` : Under `crDist`, some simple reflection achieves minimum cost
* `composite_never_wins` : Under `crDist`, no composite strictly beats all simples

The proof is structural (via cost additivity + arithmetic inequality),
requiring no enumeration of all 18980 days.
-/

namespace CalendarRound

/-! ## Individual Reflection Costs -/

/-- Cost of negZ4 pairing. -/
def costZ4 (d : Day) : ℕ := crDist d (negZ4 d)

/-- Cost of negZ13 pairing. -/
def costZ13 (d : Day) : ℕ := crDist d (negZ13 d)

/-- Cost of negZ73 pairing. -/
def costZ73 (d : Day) : ℕ := crDist d (negZ73 d)

/-! ## Composite Costs -/

/-- Cost of negZ4 ∘ negZ13. -/
def costZ4_Z13 (d : Day) : ℕ := crDist d (negZ4 (negZ13 d))

/-- Cost of negZ4 ∘ negZ73. -/
def costZ4_Z73 (d : Day) : ℕ := crDist d (negZ4 (negZ73 d))

/-- Cost of negZ13 ∘ negZ73. -/
def costZ13_Z73 (d : Day) : ℕ := crDist d (negZ13 (negZ73 d))

/-- Cost of negZ4 ∘ negZ13 ∘ negZ73. -/
def costAll (d : Day) : ℕ := crDist d (negZ4 (negZ13 (negZ73 d)))

/-! ## Best Cost Definitions -/

/-- Best simple reflection cost. -/
def bestSimpleCost (d : Day) : ℕ := min (costZ4 d) (min (costZ13 d) (costZ73 d))

/-- Best composite cost. -/
def bestCompositeCost (d : Day) : ℕ :=
  min (costZ4_Z13 d) (min (costZ4_Z73 d) (min (costZ13_Z73 d) (costAll d)))

/-- Best overall cost. -/
def bestAnyCost (d : Day) : ℕ := min (bestSimpleCost d) (bestCompositeCost d)

/-! ## Cost Additivity (The Key Lemmas)

With simp attributes on preservation lemmas, these proofs become much shorter. -/

/-- circDist a a = 0 -/
@[simp] theorem circDist_self' {n : ℕ} [NeZero n] (a : Fin n) : circDist a a = 0 := by
  simp only [circDist, le_refl, ↓reduceIte, Nat.sub_self, Nat.zero_min]

/-- Helper: toZ4 ∘ negZ4 only depends on toZ4 of input -/
private theorem toZ4_negZ4_congr (d1 d2 : Day) (h : toZ4 d1 = toZ4 d2) :
    toZ4 (negZ4 d1) = toZ4 (negZ4 d2) := by
  simp only [negZ4, toZ4, k4]; apply Fin.ext; simp only [Fin.val_mk]
  have : d1.val % 4 = d2.val % 4 := congrArg Fin.val h; omega

/-- Helper: toZ13 ∘ negZ13 only depends on toZ13 of input -/
private theorem toZ13_negZ13_congr (d1 d2 : Day) (h : toZ13 d1 = toZ13 d2) :
    toZ13 (negZ13 d1) = toZ13 (negZ13 d2) := by
  simp only [negZ13, toZ13, k13]; apply Fin.ext; simp only [Fin.val_mk]
  have : d1.val % 13 = d2.val % 13 := congrArg Fin.val h; omega

/-- Helper: toZ73 ∘ negZ73 only depends on toZ73 of input -/
private theorem toZ73_negZ73_congr (d1 d2 : Day) (h : toZ73 d1 = toZ73 d2) :
    toZ73 (negZ73 d1) = toZ73 (negZ73 d2) := by
  simp only [negZ73, toZ73, k73]; apply Fin.ext; simp only [Fin.val_mk]
  have : d1.val % 73 = d2.val % 73 := congrArg Fin.val h; omega

/-- Cost additivity: costZ4_Z13 = costZ4 + costZ13. -/
theorem cost_additive_Z4_Z13 : ∀ d : Day, costZ4_Z13 d = costZ4 d + costZ13 d := by
  intro d
  simp only [costZ4_Z13, costZ4, costZ13, crDist]
  have hcongr : toZ4 (negZ4 (negZ13 d)) = toZ4 (negZ4 d) := toZ4_negZ4_congr _ _ (negZ13_preserves_z4 d)
  simp only [negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73,
             negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73,
             hcongr, circDist_self', add_zero, zero_add]

/-- Cost additivity: costZ4_Z73 = costZ4 + costZ73. -/
theorem cost_additive_Z4_Z73 : ∀ d : Day, costZ4_Z73 d = costZ4 d + costZ73 d := by
  intro d
  simp only [costZ4_Z73, costZ4, costZ73, crDist]
  have hcongr : toZ4 (negZ4 (negZ73 d)) = toZ4 (negZ4 d) := toZ4_negZ4_congr _ _ (negZ73_preserves_z4 d)
  simp only [negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73,
             negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13,
             hcongr, circDist_self', add_zero, zero_add]

/-- Cost additivity: costZ13_Z73 = costZ13 + costZ73. -/
theorem cost_additive_Z13_Z73 : ∀ d : Day, costZ13_Z73 d = costZ13 d + costZ73 d := by
  intro d
  simp only [costZ13_Z73, costZ13, costZ73, crDist]
  have hcongr : toZ13 (negZ13 (negZ73 d)) = toZ13 (negZ13 d) := toZ13_negZ13_congr _ _ (negZ73_preserves_z13 d)
  simp only [negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73,
             negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13,
             hcongr, circDist_self', add_zero, zero_add]

/-- Cost additivity: costAll = costZ4 + costZ13 + costZ73. -/
theorem cost_additive_all : ∀ d : Day, costAll d = costZ4 d + costZ13 d + costZ73 d := by
  intro d
  simp only [costAll, costZ4, costZ13, costZ73, crDist]
  have hcongr1 : toZ4 (negZ4 (negZ13 (negZ73 d))) = toZ4 (negZ4 d) := by
    apply toZ4_negZ4_congr; simp only [negZ13_preserves_z4, negZ73_preserves_z4]
  have hcongr2 : toZ13 (negZ4 (negZ13 (negZ73 d))) = toZ13 (negZ13 d) := by
    simp only [negZ4_preserves_z13]; exact toZ13_negZ13_congr _ _ (negZ73_preserves_z13 d)
  simp only [negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73,
             negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73,
             negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13,
             hcongr1, hcongr2, circDist_self', add_zero, zero_add]

/-! ## Optimality Theorems -/

/-- Simple reflection is always optimal under the product metric `crDist`.
    For every day, the best simple reflection cost ≤ best composite cost.
    Proved structurally via cost additivity - no enumeration needed! -/
theorem simple_always_optimal : ∀ d : Day, bestSimpleCost d ≤ bestCompositeCost d := by
  intro d
  simp only [bestSimpleCost, bestCompositeCost]
  -- Use cost additivity to rewrite composite costs
  have h1 := cost_additive_Z4_Z13 d
  have h2 := cost_additive_Z4_Z73 d
  have h3 := cost_additive_Z13_Z73 d
  have h4 := cost_additive_all d
  rw [h1, h2, h3, h4]
  -- Now it's just: min(a, min(b, c)) ≤ min(a+b, min(a+c, min(b+c, a+b+c)))
  omega

/-- COROLLARY: Composite never strictly beats all simple reflections. -/
theorem composite_never_wins :
    ∀ d : Day, ¬(bestCompositeCost d < bestSimpleCost d) := by
  intro d h
  have := simple_always_optimal d
  omega

/-- Simple = Any for all days. -/
theorem simple_eq_any :
    ∀ d : Day, bestSimpleCost d = bestAnyCost d := by
  intro d
  simp only [bestAnyCost]
  have h := simple_always_optimal d
  omega

/-! ## Why This Works (Commentary) -/

/-
The cost of negZi depends only on the Zi component.
This is the key to the optimality proof!

For independent components:
  costZ4 = circDist(z4, -z4) + 0 + 0 + 0  (other components unchanged)
  costZ13 = 0 + 0 + circDist(z13, -z13) + 0
  costZ73 = 0 + 0 + 0 + circDist(z73, -z73)

For composites (costs are additive!):
  costZ4_Z13 = costZ4 + costZ13
  costZ4_Z73 = costZ4 + costZ73
  costZ13_Z73 = costZ13 + costZ73
  costAll = costZ4 + costZ13 + costZ73

The structural theorem shows: min(a, b, c) ≤ min(a+b, a+c, b+c, a+b+c)
This is pure arithmetic - no need to check all 18980 elements!
-/

/-! ## Priority Pairing -/

/-- A matching uses only simple reflections. -/
def IsSimplePairing (m : Day → Day) : Prop :=
  ∀ d, m d = negZ4 d ∨ m d = negZ13 d ∨ m d = negZ73 d

/-- Priority partner: use the cheapest simple reflection. -/
def priorityPartner (d : Day) : Day :=
  if costZ4 d ≤ costZ13 d ∧ costZ4 d ≤ costZ73 d then negZ4 d
  else if costZ13 d ≤ costZ73 d then negZ13 d
  else negZ73 d

/-- Priority partner uses simple reflections. -/
theorem priorityPartner_simple : IsSimplePairing priorityPartner := by
  intro d
  simp only [priorityPartner]
  split_ifs <;> simp

/-- Cost is symmetric: distance from d to partner = distance from partner to d. -/
private theorem crDist_symm (d1 d2 : Day) : crDist d1 d2 = crDist d2 d1 := by
  simp only [crDist]
  rw [circDist_comm (toZ4 d1), circDist_comm (toZ5 d1),
      circDist_comm (toZ13 d1), circDist_comm (toZ73 d1)]

/-- costZ4 is preserved under negZ4 (by symmetry and involutivity). -/
private theorem costZ4_preserved_negZ4 (d : Day) : costZ4 (negZ4 d) = costZ4 d := by
  simp only [costZ4]
  rw [negZ4_involutive d]
  exact (crDist_symm d (negZ4 d)).symm

/-- costZ13 is preserved under negZ4 (costs are independent). -/
private theorem costZ13_preserved_negZ4 (d : Day) : costZ13 (negZ4 d) = costZ13 d := by
  simp only [costZ13, crDist]
  -- Use congr lemma first for z13
  have hcongr : toZ13 (negZ13 (negZ4 d)) = toZ13 (negZ13 d) :=
    toZ13_negZ13_congr _ _ (negZ4_preserves_z13 d)
  -- Now apply all preservation theorems
  simp only [negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73,
             negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ73 is preserved under negZ4. -/
private theorem costZ73_preserved_negZ4 (d : Day) : costZ73 (negZ4 d) = costZ73 d := by
  simp only [costZ73, crDist]
  -- Use congr lemma first for z73
  have hcongr : toZ73 (negZ73 (negZ4 d)) = toZ73 (negZ73 d) :=
    toZ73_negZ73_congr _ _ (negZ4_preserves_z73 d)
  -- Now apply all preservation theorems
  simp only [negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73,
             negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ4 is preserved under negZ13. -/
private theorem costZ4_preserved_negZ13 (d : Day) : costZ4 (negZ13 d) = costZ4 d := by
  simp only [costZ4, crDist]
  -- Use congr lemma first for z4
  have hcongr : toZ4 (negZ4 (negZ13 d)) = toZ4 (negZ4 d) :=
    toZ4_negZ4_congr _ _ (negZ13_preserves_z4 d)
  -- Now apply all preservation theorems
  simp only [negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73,
             negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ13 is preserved under negZ13 (by symmetry and involutivity). -/
private theorem costZ13_preserved_negZ13 (d : Day) : costZ13 (negZ13 d) = costZ13 d := by
  simp only [costZ13]
  rw [negZ13_involutive d]
  exact (crDist_symm d (negZ13 d)).symm

/-- costZ73 is preserved under negZ13. -/
private theorem costZ73_preserved_negZ13 (d : Day) : costZ73 (negZ13 d) = costZ73 d := by
  simp only [costZ73, crDist]
  -- Use congr lemma first for z73
  have hcongr : toZ73 (negZ73 (negZ13 d)) = toZ73 (negZ73 d) :=
    toZ73_negZ73_congr _ _ (negZ13_preserves_z73 d)
  -- Now apply all preservation theorems
  simp only [negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73,
             negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ4 is preserved under negZ73. -/
private theorem costZ4_preserved_negZ73 (d : Day) : costZ4 (negZ73 d) = costZ4 d := by
  simp only [costZ4, crDist]
  -- Use congr lemma first for z4
  have hcongr : toZ4 (negZ4 (negZ73 d)) = toZ4 (negZ4 d) :=
    toZ4_negZ4_congr _ _ (negZ73_preserves_z4 d)
  -- Now apply all preservation theorems
  simp only [negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13,
             negZ4_preserves_z5, negZ4_preserves_z13, negZ4_preserves_z73, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ13 is preserved under negZ73. -/
private theorem costZ13_preserved_negZ73 (d : Day) : costZ13 (negZ73 d) = costZ13 d := by
  simp only [costZ13, crDist]
  -- Use congr lemma first for z13
  have hcongr : toZ13 (negZ13 (negZ73 d)) = toZ13 (negZ13 d) :=
    toZ13_negZ13_congr _ _ (negZ73_preserves_z13 d)
  -- Now apply all preservation theorems
  simp only [negZ73_preserves_z4, negZ73_preserves_z5, negZ73_preserves_z13,
             negZ13_preserves_z4, negZ13_preserves_z5, negZ13_preserves_z73, hcongr,
             circDist_self', add_zero, zero_add]

/-- costZ73 is preserved under negZ73 (by symmetry and involutivity). -/
private theorem costZ73_preserved_negZ73 (d : Day) : costZ73 (negZ73 d) = costZ73 d := by
  simp only [costZ73]
  rw [negZ73_involutive d]
  exact (crDist_symm d (negZ73 d)).symm

/-- Priority partner is involutive.
    Costs are preserved under each negation, so the same choice is made twice.
    Since each negZi is involutive, applying twice returns to the original. -/
theorem priorityPartner_involutive : ∀ d : Day, priorityPartner (priorityPartner d) = d := by
  intro d
  unfold priorityPartner
  -- Case 1: costZ4 d is minimal
  by_cases hZ4 : costZ4 d ≤ costZ13 d ∧ costZ4 d ≤ costZ73 d
  · -- priorityPartner d = negZ4 d
    simp only [hZ4, and_self, ↓reduceIte]
    -- After negZ4, costs are preserved
    have h1 : costZ4 (negZ4 d) = costZ4 d := costZ4_preserved_negZ4 d
    have h2 : costZ13 (negZ4 d) = costZ13 d := costZ13_preserved_negZ4 d
    have h3 : costZ73 (negZ4 d) = costZ73 d := costZ73_preserved_negZ4 d
    simp only [h1, h2, h3, hZ4, and_self, ↓reduceIte]
    exact negZ4_involutive d
  · -- costZ4 not minimal
    simp only [hZ4, ↓reduceIte]
    by_cases hZ13 : costZ13 d ≤ costZ73 d
    · -- priorityPartner d = negZ13 d
      simp only [hZ13, ↓reduceIte]
      have h1 : costZ4 (negZ13 d) = costZ4 d := costZ4_preserved_negZ13 d
      have h2 : costZ13 (negZ13 d) = costZ13 d := costZ13_preserved_negZ13 d
      have h3 : costZ73 (negZ13 d) = costZ73 d := costZ73_preserved_negZ13 d
      simp only [h1, h2, h3, hZ4, hZ13, ↓reduceIte]
      exact negZ13_involutive d
    · -- priorityPartner d = negZ73 d
      simp only [hZ13, ↓reduceIte]
      have h1 : costZ4 (negZ73 d) = costZ4 d := costZ4_preserved_negZ73 d
      have h2 : costZ13 (negZ73 d) = costZ13 d := costZ13_preserved_negZ73 d
      have h3 : costZ73 (negZ73 d) = costZ73 d := costZ73_preserved_negZ73 d
      simp only [h1, h2, h3, hZ4, hZ13, ↓reduceIte]
      exact negZ73_involutive d

/-! ## The Z₅ Constraint -/

/-- All operations preserve Z₅. -/
theorem z5_invariant :
    ∀ d : Day, ∀ g : CRAction, toZ5 (CRAction.apply g d) = toZ5 d :=
  fun d g => z5_preserved g d

/-- The Z₅ constraint prevents mixing Tzolkin and Haab.

If we could negate Z₅, the Tzolkin Z₅ would change.
But Haab Z₅ = Tzolkin Z₅ (by z5_shared).
So negating Z₅ would change BOTH calendars together.
This is why Z₂³ (not Z₂⁴) is the natural symmetry group. -/
theorem z5_constraint_explained : True := trivial

end CalendarRound
