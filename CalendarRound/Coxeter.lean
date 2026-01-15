import CalendarRound.Basic
import Mathlib.Tactic.FinCases

/-!
# Coxeter Structure on Calendar Round

The natural symmetry group is Z₂³ acting on (Z₄, Z₁₃, Z₇₃).

## The Z₅ Constraint

Since Z₅ is shared between Tzolkin and Haab, we cannot negate it
if we want the symmetries to respect both calendar systems.

The key insight: GCD(260, 365) = 5 forces the symmetry group
to preserve the Z₅ component.

## Available Simple Reflections

- neg_Z4: Negate Z₄ component (cardinal direction flip in veintena)
- neg_Z13: Negate Z₁₃ component (trecena reflection)
- neg_Z73: Negate Z₇₃ component (Haab year reflection)

## Main Results

* Symmetry reduction Z₂⁴ → Z₂³ forced by fiber structure (metric-independent)
* Z₅ preserved by all group actions (metric-independent, proven below)
* Simple reflections optimal under product metric (see Optimality.lean)

Note: Orbit-counting statistics (3885 orbits, 777 per Z₅ class) are informational
and not used in the optimality proofs.
-/

namespace CalendarRound

/-! ## CRT Coefficients

The Calendar Round Z₁₈₉₈₀ = Z₄ × Z₅ × Z₁₃ × Z₇₃ uses these CRT coefficients:
- k₄ = 4745:  4745 ≡ 1 (mod 4), 4745 ≡ 0 (mod 5, 13, 73)
- k₁₃ = 14600: 14600 ≡ 1 (mod 13), 14600 ≡ 0 (mod 4, 5, 73)
- k₇₃ = 14820: 14820 ≡ 1 (mod 73), 14820 ≡ 0 (mod 4, 5, 13)
-/

def k4 : ℕ := 4745
def k13 : ℕ := 14600
def k73 : ℕ := 14820

-- CRT coefficient properties (small number facts, decidable)
theorem k4_mod4 : k4 % 4 = 1 := by native_decide
theorem k4_mod5 : k4 % 5 = 0 := by native_decide
theorem k4_mod13 : k4 % 13 = 0 := by native_decide
theorem k4_mod73 : k4 % 73 = 0 := by native_decide

theorem k13_mod4 : k13 % 4 = 0 := by native_decide
theorem k13_mod5 : k13 % 5 = 0 := by native_decide
theorem k13_mod13 : k13 % 13 = 1 := by native_decide
theorem k13_mod73 : k13 % 73 = 0 := by native_decide

theorem k73_mod4 : k73 % 4 = 0 := by native_decide
theorem k73_mod5 : k73 % 5 = 0 := by native_decide
theorem k73_mod13 : k73 % 13 = 0 := by native_decide
theorem k73_mod73 : k73 % 73 = 1 := by native_decide

/-! ## Negation Operations -/

/-- Negate Z₄ component: d ↦ d - 2·z₄·k₄ (mod 18980). -/
def negZ4 (d : Day) : Day :=
  let z4 := toZ4 d
  let offset := (2 * z4.val * k4) % 18980
  ⟨(d.val + 18980 - offset) % 18980, Nat.mod_lt _ (by omega)⟩

/-- Negate Z₁₃ component: d ↦ d - 2·z₁₃·k₁₃ (mod 18980). -/
def negZ13 (d : Day) : Day :=
  let z13 := toZ13 d
  let offset := (2 * z13.val * k13) % 18980
  ⟨(d.val + 18980 - offset) % 18980, Nat.mod_lt _ (by omega)⟩

/-- Negate Z₇₃ component: d ↦ d - 2·z₇₃·k₇₃ (mod 18980). -/
def negZ73 (d : Day) : Day :=
  let z73 := toZ73 d
  let offset := (2 * z73.val * k73) % 18980
  ⟨(d.val + 18980 - offset) % 18980, Nat.mod_lt _ (by omega)⟩

/-! ## Preservation Theorems

Key insight: Since k₄ ≡ 0 (mod 5, 13, 73), subtracting 2·z₄·k₄ preserves Z₅, Z₁₃, Z₇₃.
Similarly for k₁₃ and k₇₃.

Strategy: Case split on the small component (z4 ∈ Fin 4, z13 ∈ Fin 13, z73 ∈ Fin 73)
using fin_cases, then native_decide on each case.
-/

-- Helper: offset from Z4 negation is divisible by 5, 13, 73
private theorem offset_z4_mod5 (z4 : Fin 4) : (2 * z4.val * k4) % 18980 % 5 = 0 := by
  fin_cases z4 <;> native_decide

private theorem offset_z4_mod13 (z4 : Fin 4) : (2 * z4.val * k4) % 18980 % 13 = 0 := by
  fin_cases z4 <;> native_decide

private theorem offset_z4_mod73 (z4 : Fin 4) : (2 * z4.val * k4) % 18980 % 73 = 0 := by
  fin_cases z4 <;> native_decide

-- Helper: offset from Z13 negation is divisible by 4, 5, 73
private theorem offset_z13_mod4 (z13 : Fin 13) : (2 * z13.val * k13) % 18980 % 4 = 0 := by
  fin_cases z13 <;> native_decide

private theorem offset_z13_mod5 (z13 : Fin 13) : (2 * z13.val * k13) % 18980 % 5 = 0 := by
  fin_cases z13 <;> native_decide

private theorem offset_z13_mod73 (z13 : Fin 13) : (2 * z13.val * k13) % 18980 % 73 = 0 := by
  fin_cases z13 <;> native_decide

-- Helper: offset from Z73 negation is divisible by 4, 5, 13
private theorem offset_z73_mod4 (z73 : Fin 73) : (2 * z73.val * k73) % 18980 % 4 = 0 := by
  fin_cases z73 <;> native_decide

private theorem offset_z73_mod5 (z73 : Fin 73) : (2 * z73.val * k73) % 18980 % 5 = 0 := by
  fin_cases z73 <;> native_decide

private theorem offset_z73_mod13 (z73 : Fin 73) : (2 * z73.val * k73) % 18980 % 13 = 0 := by
  fin_cases z73 <;> native_decide

-- Main preservation theorems using the helper lemmas

/-- negZ4 preserves Z₅. -/
theorem negZ4_preserves_z5 : ∀ d : Day, toZ5 (negZ4 d) = toZ5 d := by
  intro d
  simp only [negZ4, toZ5, toZ4, k4]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z4_mod5 ⟨d.val % 4, Nat.mod_lt _ (by omega)⟩
  simp only [k4, Fin.val_mk] at h1
  have h2 : 18980 % 5 = 0 := by native_decide
  have h3 : 5 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ4 preserves Z₁₃. -/
theorem negZ4_preserves_z13 : ∀ d : Day, toZ13 (negZ4 d) = toZ13 d := by
  intro d
  simp only [negZ4, toZ13, toZ4, k4]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z4_mod13 ⟨d.val % 4, Nat.mod_lt _ (by omega)⟩
  simp only [k4, Fin.val_mk] at h1
  have h2 : 18980 % 13 = 0 := by native_decide
  have h3 : 13 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ4 preserves Z₇₃. -/
theorem negZ4_preserves_z73 : ∀ d : Day, toZ73 (negZ4 d) = toZ73 d := by
  intro d
  simp only [negZ4, toZ73, toZ4, k4]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z4_mod73 ⟨d.val % 4, Nat.mod_lt _ (by omega)⟩
  simp only [k4, Fin.val_mk] at h1
  have h2 : 18980 % 73 = 0 := by native_decide
  have h3 : 73 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ13 preserves Z₄. -/
theorem negZ13_preserves_z4 : ∀ d : Day, toZ4 (negZ13 d) = toZ4 d := by
  intro d
  simp only [negZ13, toZ4, toZ13, k13]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z13_mod4 ⟨d.val % 13, Nat.mod_lt _ (by omega)⟩
  simp only [k13, Fin.val_mk] at h1
  have h2 : 18980 % 4 = 0 := by native_decide
  have h3 : 4 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ13 preserves Z₅. -/
theorem negZ13_preserves_z5 : ∀ d : Day, toZ5 (negZ13 d) = toZ5 d := by
  intro d
  simp only [negZ13, toZ5, toZ13, k13]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z13_mod5 ⟨d.val % 13, Nat.mod_lt _ (by omega)⟩
  simp only [k13, Fin.val_mk] at h1
  have h2 : 18980 % 5 = 0 := by native_decide
  have h3 : 5 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ13 preserves Z₇₃. -/
theorem negZ13_preserves_z73 : ∀ d : Day, toZ73 (negZ13 d) = toZ73 d := by
  intro d
  simp only [negZ13, toZ73, toZ13, k13]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z13_mod73 ⟨d.val % 13, Nat.mod_lt _ (by omega)⟩
  simp only [k13, Fin.val_mk] at h1
  have h2 : 18980 % 73 = 0 := by native_decide
  have h3 : 73 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ73 preserves Z₄. -/
theorem negZ73_preserves_z4 : ∀ d : Day, toZ4 (negZ73 d) = toZ4 d := by
  intro d
  simp only [negZ73, toZ4, toZ73, k73]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z73_mod4 ⟨d.val % 73, Nat.mod_lt _ (by omega)⟩
  simp only [k73, Fin.val_mk] at h1
  have h2 : 18980 % 4 = 0 := by native_decide
  have h3 : 4 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ73 preserves Z₅. -/
theorem negZ73_preserves_z5 : ∀ d : Day, toZ5 (negZ73 d) = toZ5 d := by
  intro d
  simp only [negZ73, toZ5, toZ73, k73]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z73_mod5 ⟨d.val % 73, Nat.mod_lt _ (by omega)⟩
  simp only [k73, Fin.val_mk] at h1
  have h2 : 18980 % 5 = 0 := by native_decide
  have h3 : 5 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-- negZ73 preserves Z₁₃. -/
theorem negZ73_preserves_z13 : ∀ d : Day, toZ13 (negZ73 d) = toZ13 d := by
  intro d
  simp only [negZ73, toZ13, toZ73, k73]
  apply Fin.ext; simp only [Fin.val_mk]
  have h1 := offset_z73_mod13 ⟨d.val % 73, Nat.mod_lt _ (by omega)⟩
  simp only [k73, Fin.val_mk] at h1
  have h2 : 18980 % 13 = 0 := by native_decide
  have h3 : 13 ∣ 18980 := by omega
  rw [Nat.mod_mod_of_dvd _ h3]
  omega

/-! ## Simp Lemmas for Preservation

Adding @[simp] attributes allows automation to handle cost additivity proofs. -/

attribute [simp] negZ4_preserves_z5 negZ4_preserves_z13 negZ4_preserves_z73
attribute [simp] negZ13_preserves_z4 negZ13_preserves_z5 negZ13_preserves_z73
attribute [simp] negZ73_preserves_z4 negZ73_preserves_z5 negZ73_preserves_z13

/-! ## Involutivity

The key insight for involutivity: negZi(negZi(d)) = d.

For negZ4: d ↦ d - 2·z₄·k₄ where z₄ = d mod 4.
After first application: z₄' = (4 - z₄) mod 4.
Total offset: 2·z₄·k₄ + 2·z₄'·k₄ = 2·4·k₄ = 8·4745 = 37960 = 2·18980 ≡ 0 (mod 18980).
-/

/-- The offset for Z4 negation. -/
private def offsetZ4 (z4 : ℕ) : ℕ := (2 * z4 * k4) % 18980

/-- The offset for Z13 negation. -/
private def offsetZ13 (z13 : ℕ) : ℕ := (2 * z13 * k13) % 18980

/-- The offset for Z73 negation. -/
private def offsetZ73 (z73 : ℕ) : ℕ := (2 * z73 * k73) % 18980

/-- Double offset for Z4 sums to 0 or 18980. -/
private theorem double_offset_z4_eq (z4 : Fin 4) :
    offsetZ4 z4.val + offsetZ4 ((4 - z4.val) % 4) = 0 ∨
    offsetZ4 z4.val + offsetZ4 ((4 - z4.val) % 4) = 18980 := by
  fin_cases z4 <;> simp only [offsetZ4, k4] <;> native_decide

/-- Double offset for Z13 sums to 0 or 18980. -/
private theorem double_offset_z13_eq (z13 : Fin 13) :
    offsetZ13 z13.val + offsetZ13 ((13 - z13.val) % 13) = 0 ∨
    offsetZ13 z13.val + offsetZ13 ((13 - z13.val) % 13) = 18980 := by
  fin_cases z13 <;> simp only [offsetZ13, k13] <;> native_decide

/-- Double offset for Z73 sums to 0 or 18980. -/
private theorem double_offset_z73_eq (z73 : Fin 73) :
    offsetZ73 z73.val + offsetZ73 ((73 - z73.val) % 73) = 0 ∨
    offsetZ73 z73.val + offsetZ73 ((73 - z73.val) % 73) = 18980 := by
  fin_cases z73 <;> simp only [offsetZ73, k73] <;> native_decide

/-- negZ4 is involutive. -/
theorem negZ4_involutive : Function.Involutive negZ4 := by
  intro d
  apply Fin.ext
  unfold negZ4 toZ4
  simp only [Fin.val_mk, k4]
  have hlt : d.val < 18980 := d.isLt
  have hz4 : d.val % 4 < 4 := Nat.mod_lt _ (by omega)
  have hdbl := double_offset_z4_eq ⟨d.val % 4, hz4⟩
  simp only [offsetZ4, k4, Fin.val_mk] at hdbl
  rcases hdbl with hdbl | hdbl <;> omega

/-- negZ13 is involutive. -/
theorem negZ13_involutive : Function.Involutive negZ13 := by
  intro d
  apply Fin.ext
  unfold negZ13 toZ13
  simp only [Fin.val_mk, k13]
  have hlt : d.val < 18980 := d.isLt
  have hz13 : d.val % 13 < 13 := Nat.mod_lt _ (by omega)
  have hdbl := double_offset_z13_eq ⟨d.val % 13, hz13⟩
  simp only [offsetZ13, k13, Fin.val_mk] at hdbl
  rcases hdbl with hdbl | hdbl <;> omega

/-- negZ73 is involutive. -/
theorem negZ73_involutive : Function.Involutive negZ73 := by
  intro d
  apply Fin.ext
  unfold negZ73 toZ73
  simp only [Fin.val_mk, k73]
  have hlt : d.val < 18980 := d.isLt
  have hz73 : d.val % 73 < 73 := Nat.mod_lt _ (by omega)
  have hdbl := double_offset_z73_eq ⟨d.val % 73, hz73⟩
  simp only [offsetZ73, k73, Fin.val_mk] at hdbl
  rcases hdbl with hdbl | hdbl <;> omega

/-! ## The Z₂³ Group -/

/-- Elements of Z₂³ = Z₂ × Z₂ × Z₂. -/
inductive CRAction
  | e     -- identity
  | n4    -- negate Z₄
  | n13   -- negate Z₁₃
  | n73   -- negate Z₇₃
  | n4_13   -- negate Z₄ and Z₁₃
  | n4_73   -- negate Z₄ and Z₇₃
  | n13_73  -- negate Z₁₃ and Z₇₃
  | n4_13_73 -- negate all three
  deriving DecidableEq, Repr

namespace CRAction

instance : Fintype CRAction := ⟨⟨[e, n4, n13, n73, n4_13, n4_73, n13_73, n4_13_73], by decide⟩,
  by intro x; cases x <;> decide⟩

/-- Apply action to a Calendar Round day. -/
def apply : CRAction → Day → Day
  | e => id
  | n4 => negZ4
  | n13 => negZ13
  | n73 => negZ73
  | n4_13 => negZ4 ∘ negZ13
  | n4_73 => negZ4 ∘ negZ73
  | n13_73 => negZ13 ∘ negZ73
  | n4_13_73 => negZ4 ∘ negZ13 ∘ negZ73

/-- Group multiplication (XOR on sign bits). -/
def mul : CRAction → CRAction → CRAction
  | e, g => g
  | g, e => g
  | n4, n4 => e
  | n13, n13 => e
  | n73, n73 => e
  | n4, n13 => n4_13
  | n13, n4 => n4_13
  | n4, n73 => n4_73
  | n73, n4 => n4_73
  | n13, n73 => n13_73
  | n73, n13 => n13_73
  | n4_13, n4 => n13
  | n4, n4_13 => n13
  | n4_13, n13 => n4
  | n13, n4_13 => n4
  | n4_73, n4 => n73
  | n4, n4_73 => n73
  | n4_73, n73 => n4
  | n73, n4_73 => n4
  | n13_73, n13 => n73
  | n13, n13_73 => n73
  | n13_73, n73 => n13
  | n73, n13_73 => n13
  | n4_13, n73 => n4_13_73
  | n73, n4_13 => n4_13_73
  | n4_73, n13 => n4_13_73
  | n13, n4_73 => n4_13_73
  | n13_73, n4 => n4_13_73
  | n4, n13_73 => n4_13_73
  | n4_13_73, n4 => n13_73
  | n4, n4_13_73 => n13_73
  | n4_13_73, n13 => n4_73
  | n13, n4_13_73 => n4_73
  | n4_13_73, n73 => n4_13
  | n73, n4_13_73 => n4_13
  | n4_13, n4_13 => e
  | n4_73, n4_73 => e
  | n13_73, n13_73 => e
  | n4_13_73, n4_13_73 => e
  | n4_13, n4_73 => n13_73
  | n4_73, n4_13 => n13_73
  | n4_13, n13_73 => n4_73
  | n13_73, n4_13 => n4_73
  | n4_73, n13_73 => n4_13
  | n13_73, n4_73 => n4_13
  | n4_13_73, n4_13 => n73
  | n4_13, n4_13_73 => n73
  | n4_13_73, n4_73 => n13
  | n4_73, n4_13_73 => n13
  | n4_13_73, n13_73 => n4
  | n13_73, n4_13_73 => n4

instance : One CRAction := ⟨e⟩
instance : Mul CRAction := ⟨mul⟩
instance : Inv CRAction := ⟨id⟩  -- All elements are self-inverse

theorem mul_assoc (a b c : CRAction) : mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem one_mul (a : CRAction) : mul e a = a := by cases a <;> rfl
theorem mul_one (a : CRAction) : mul a e = a := by cases a <;> rfl
theorem inv_mul (a : CRAction) : mul a a = e := by cases a <;> rfl

instance : Group CRAction where
  mul := mul
  mul_assoc := mul_assoc
  one := e
  one_mul := one_mul
  mul_one := mul_one
  inv := id
  inv_mul_cancel := inv_mul

end CRAction

/-! ## Simple Reflections -/

/-- The simple reflections: {n4, n13, n73}. -/
def crGenerators : Finset CRAction := {.n4, .n13, .n73}

/-- Simple reflections are exactly the length-1 elements. -/
def isSimple (g : CRAction) : Bool := g = .n4 || g = .n13 || g = .n73

theorem n4_simple : isSimple CRAction.n4 = true := rfl
theorem n13_simple : isSimple CRAction.n13 = true := rfl
theorem n73_simple : isSimple CRAction.n73 = true := rfl

/-! ## Orbit Structure (Informational)

The following orbit counts are computed externally and included for reference.
They are NOT used in the optimality proofs, which are fully structural.
-/

-- Orbit statistics (informational only, not used in proofs):
-- - Number of orbits under Z₂³: 3885
-- - Orbits per Z₅ class: 777

/-- 3885 = 777 × 5. -/
theorem orbit_count_factorization : 3885 = 777 * 5 := by omega

/-- Z₅ is preserved by all actions. (Follows from axioms on simple reflections) -/
theorem z5_preserved (g : CRAction) (d : Day) : toZ5 (CRAction.apply g d) = toZ5 d := by
  cases g
  case e => rfl
  case n4 => exact negZ4_preserves_z5 d
  case n13 => exact negZ13_preserves_z5 d
  case n73 => exact negZ73_preserves_z5 d
  case n4_13 =>
    simp only [CRAction.apply, Function.comp_apply]
    rw [negZ4_preserves_z5, negZ13_preserves_z5]
  case n4_73 =>
    simp only [CRAction.apply, Function.comp_apply]
    rw [negZ4_preserves_z5, negZ73_preserves_z5]
  case n13_73 =>
    simp only [CRAction.apply, Function.comp_apply]
    rw [negZ13_preserves_z5, negZ73_preserves_z5]
  case n4_13_73 =>
    simp only [CRAction.apply, Function.comp_apply]
    rw [negZ4_preserves_z5, negZ13_preserves_z5, negZ73_preserves_z5]

end CalendarRound
